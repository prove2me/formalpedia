-- Prove2me | solution 1 for PigeonholeDesign.Upper.Supplement.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:21.89105+00:00
-- url     : https://prove2.me/submissions/60bcd58d-038c-4278-9e3b-624c031fe6c5

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

open PigeonholeDesign
open PigeonholeDesign.Upper
open PigeonholeDesign.Upper.Supplement

theorem solution (p q : ℕ) (hp : 2 ≤ p) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      (∀ x : Fin T → MultiDim.Cov q p, MultiDim.Admissible S x →
          mpdDisc x ≤ C * (T : ℝ) ^ (((p : ℝ) - 1) / p)) ∧
      (∃ x : Fin T → MultiDim.Cov q p, MultiDim.Admissible S x ∧
          c * (T : ℝ) ^ (((p : ℝ) - 1) / p) ≤ mpdDisc x) := by
            classical
            have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
            set α : ℝ := ((p : ℝ) - 1) / p with hα
            have hαhalf : (1:ℝ)/2 ≤ α := by
              rw [hα, le_div_iff₀ (by linarith only [hpR])]; linarith only [hpR]
            have hα1 : α ≤ 1 := by rw [hα, div_le_one (by linarith only [hpR])]; linarith only [hpR]
            have hsplit : ∀ n : ℝ, 0 < n → n ^ α * n ^ ((p:ℝ)⁻¹) = n := by
              intro n hn
              rw [← Real.rpow_add hn]
              have : α + (p:ℝ)⁻¹ = 1 := by rw [hα]; field_simp; ring
              rw [this, Real.rpow_one]
            have hdist_le_sum : ∀ u v : MultiDim.Cov q p, dist u v ≤ ∑ k, dist (u k) (v k) := by
              intro u v
              rw [EuclideanSpace.dist_eq]
              calc √(∑ k, dist (u k) (v k) ^ 2) ≤ √((∑ k, dist (u k) (v k)) ^ 2) :=
                    Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => dist_nonneg))
                _ = ∑ k, dist (u k) (v k) := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => dist_nonneg)
            set D : ℝ := (q:ℝ) + p with hD
            have hDpos : 0 < D := by rw [hD]; positivity
            have hcoord : ∀ (T : ℕ) (x : Fin T → MultiDim.Cov q p), MultiDim.Admissible S x →
                ∀ t k, x t k ∈ Set.Icc (0:ℝ) 1 := by
              intro T x hx t k
              rcases k with i | j
              · exact hS i (hx.1 t i)
              · exact hx.2 t j
            have diam : ∀ u v : MultiDim.Cov q p, (∀ k, u k ∈ Set.Icc (0:ℝ) 1) → (∀ k, v k ∈ Set.Icc (0:ℝ) 1) →
                dist u v ≤ D := by
              intro u v hu hv
              refine (hdist_le_sum u v).trans ?_
              calc ∑ k, dist (u k) (v k) ≤ ∑ _k : Fin q ⊕ Fin p, (1:ℝ) := by
                    refine Finset.sum_le_sum fun k _ => ?_
                    rw [Real.dist_eq, abs_le]
                    have := hu k; have := hv k
                    constructor <;> linarith only [(hv k).1, (hv k).2, (hu k).1, (hu k).2]
                _ = D := by simp [hD]
            set N : ℕ := ∏ i, (S i).card with hN
            have hN1 : 1 ≤ N := by
              rw [hN]
              exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => (Finset.card_pos.2 (hne i)).ne')
            have hN1R : (1:ℝ) ≤ N := by exact_mod_cast hN1
            set C₁ : ℝ := 6 * N * D with hC₁
            have close : ∀ (T : ℕ) (x : Fin T → MultiDim.Cov q p), MultiDim.Admissible S x →
                ∀ A : Finset (Fin T), 2 ≤ A.card → ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧
                  dist (x a) (x b) ≤ C₁ / (A.card : ℝ) ^ ((p:ℝ)⁻¹) := by
              intro T x hx A hA
              have hnR : (2:ℝ) ≤ A.card := by exact_mod_cast hA
              set r : ℝ := (A.card:ℝ) ^ ((p:ℝ)⁻¹) with hr_def
              have hr : 0 < r := Real.rpow_pos_of_pos (by linarith only [hnR]) _
              have hrp : r ^ p = A.card := Real.rpow_inv_natCast_pow (by linarith only [hnR]) (by omega)
              by_cases hsmall : r < 6 * N
              · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < A.card)
                refine ⟨a, ha, b, hb, hab, ?_⟩
                calc dist (x a) (x b) ≤ D := diam _ _ (hcoord T x hx a) (hcoord T x hx b)
                  _ ≤ C₁ / r := by rw [le_div_iff₀ hr, hC₁]; linarith only [mul_le_mul_of_nonneg_left hsmall.le hDpos.le]
              · push_neg at hsmall
                set m := ⌊r / (3 * N)⌋₊ with hm
                have hm1 : r / (3 * N) - 1 < m := Nat.sub_one_lt_floor _
                have h6 : 1 ≤ r / (6 * N) := by rw [le_div_iff₀ (by positivity)]; linarith only [hsmall]
                have h36 : r / (3 * N) = 2 * (r / (6 * N)) := by field_simp; ring
                have h26 : r / (2 * N) = 3 * (r / (6 * N)) := by field_simp; ring
                have hm2 : (m:ℝ) ≤ r / (3 * N) := Nat.floor_le (by positivity)
                have hmlow : r / (6 * N) ≤ m := by linarith only [hm1, h36, h6]
                have hmpos : (0:ℝ) < m := by linarith only [hmlow, h6]
                have hcard : N * (m + 1) ^ p < A.card := by
                  have hm3 : (m:ℝ) + 1 ≤ r / (2 * N) := by linarith only [hm2, h36, h26, h6]
                  have h4 : ((m:ℝ) + 1) ^ p ≤ (r / (2 * N)) ^ p := pow_le_pow_left₀ (by positivity) hm3 p
                  rw [div_pow, hrp] at h4
                  have h5 : (N:ℝ) < (2 * N) ^ p :=
                    lt_of_lt_of_le (by linarith only [hN1R]) (le_self_pow₀ (by linarith only [hN1R]) (by omega))
                  have h7 : (N:ℝ) * ((m:ℝ) + 1) ^ p < A.card := by
                    calc (N:ℝ) * ((m:ℝ) + 1) ^ p ≤ N * (A.card / (2 * N) ^ p) := by gcongr
                      _ = A.card * (N / (2 * N) ^ p) := by ring
                      _ < A.card * 1 := by
                          gcongr
                          rw [div_lt_one (by positivity)]; exact h5
                      _ = A.card := mul_one _
                  exact_mod_cast h7
                let h : Fin T → (Fin q → ℝ) × (Fin p → ℕ) :=
                  fun t => (fun i => x t (Sum.inl i), fun j => ⌊x t (Sum.inr j) * m⌋₊)
                have hmaps : ∀ t ∈ A, h t ∈ Fintype.piFinset S ×ˢ
                    Fintype.piFinset (fun _ : Fin p => Finset.range (m + 1)) := by
                  intro t _
                  simp only [h, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
                  refine ⟨fun i => hx.1 t i, fun j => ?_⟩
                  have := hx.2 t j
                  exact Nat.lt_succ_of_le (Nat.floor_le_of_le (mul_le_of_le_one_left hmpos.le this.2))
                have hct : (Fintype.piFinset S ×ˢ
                    Fintype.piFinset (fun _ : Fin p => Finset.range (m + 1))).card = N * (m + 1) ^ p := by
                  simp [Finset.card_product, Fintype.card_piFinset, hN]
                obtain ⟨a, ha, b, hb, hab, hh⟩ :=
                  Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hct]; exact hcard) hmaps
                refine ⟨a, ha, b, hb, hab, ?_⟩
                have hinl : ∀ i, x a (Sum.inl i) = x b (Sum.inl i) :=
                  fun i => congrFun (congrArg Prod.fst hh) i
                have hinr : ∀ j, ⌊x a (Sum.inr j) * m⌋₊ = ⌊x b (Sum.inr j) * m⌋₊ :=
                  fun j => congrFun (congrArg Prod.snd hh) j
                have hj : ∀ j, dist (x a (Sum.inr j)) (x b (Sum.inr j)) ≤ 1 / m := by
                  intro j
                  have ha0 := (hx.2 a j).1
                  have hb0 := (hx.2 b j).1
                  have e1 := Nat.floor_le (mul_nonneg ha0 hmpos.le)
                  have e2 := Nat.lt_floor_add_one (x a (Sum.inr j) * m)
                  have e3 := Nat.floor_le (mul_nonneg hb0 hmpos.le)
                  have e4 := Nat.lt_floor_add_one (x b (Sum.inr j) * m)
                  rw [hinr j] at e1 e2
                  rw [Real.dist_eq, abs_sub_le_iff]
                  constructor <;> rw [le_div_iff₀ hmpos] <;> linarith only [e1, e2, e3, e4]
                calc dist (x a) (x b) ≤ ∑ k, dist (x a k) (x b k) := hdist_le_sum _ _
                  _ = ∑ i, dist (x a (Sum.inl i)) (x b (Sum.inl i)) +
                      ∑ j, dist (x a (Sum.inr j)) (x b (Sum.inr j)) := Fintype.sum_sum_type _
                  _ ≤ ∑ _i : Fin q, (0:ℝ) + ∑ _j : Fin p, 1 / (m:ℝ) := by
                      gcongr with i _ j
                      · rw [hinl i, dist_self]
                      · exact hj j
                  _ = p / m := by simp [div_eq_mul_inv]
                  _ ≤ D / m := by gcongr; rw [hD]; linarith only [(q.cast_nonneg : (0:ℝ) ≤ q)]
                  _ ≤ D / (r / (6 * N)) := div_le_div_of_nonneg_left hDpos.le (by linarith only [h6]) hmlow
                  _ = C₁ / r := by rw [hC₁]; field_simp
            set K : ℝ := 2 * C₁ with hK
            have hKpos : 0 < K := by rw [hK, hC₁]; positivity
            have step : ∀ n : ℝ, 2 ≤ n → K * (n - 2) ^ α + 2 * (C₁ / n ^ ((p:ℝ)⁻¹)) ≤ K * n ^ α := by
              intro n hn
              have hn0 : 0 < n := by linarith only [hn]
              have hr : 0 < n ^ ((p:ℝ)⁻¹) := Real.rpow_pos_of_pos hn0 _
              have hsp := hsplit n hn0
              have hb : (n - 2) ^ α ≤ n ^ α * (1 + α * (-2 / n)) := by
                have h2n : 2 / n ≤ 1 := by rw [div_le_one hn0]; exact hn
                have h1 : n - 2 = n * (1 + (-2 / n)) := by field_simp; ring
                have hneg : -2 / n = -(2 / n) := by ring
                rw [h1, Real.mul_rpow hn0.le (by rw [hneg]; linarith only [h2n])]
                have hpos : 0 ≤ n ^ α := Real.rpow_nonneg hn0.le _
                refine mul_le_mul_of_nonneg_left ?_ hpos
                exact rpow_one_add_le_one_add_mul_self (by rw [hneg]; linarith only [h2n]) (by linarith only [hαhalf]) hα1
              have hA : n ^ α = n / n ^ ((p:ℝ)⁻¹) := by rw [eq_div_iff hr.ne']; exact hsp
              have key : n ^ α * (1 + α * (-2 / n)) = n / n ^ ((p:ℝ)⁻¹) - 2 * α / n ^ ((p:ℝ)⁻¹) := by
                rw [hA]; field_simp; ring
              have hC0 : 0 ≤ C₁ := by rw [hC₁]; positivity
              have hCK : C₁ ≤ K * α := by rw [hK]; linarith only [mul_le_mul_of_nonneg_left hαhalf hC0]
              have h3 : 2 * (C₁ / n ^ ((p:ℝ)⁻¹)) ≤ K * (2 * α / n ^ ((p:ℝ)⁻¹)) := by
                rw [show K * (2 * α / n ^ ((p:ℝ)⁻¹)) = 2 * (K * α) / n ^ ((p:ℝ)⁻¹) by ring,
                  show 2 * (C₁ / n ^ ((p:ℝ)⁻¹)) = 2 * C₁ / n ^ ((p:ℝ)⁻¹) by ring]
                exact div_le_div_of_nonneg_right (by linarith only [hCK]) hr.le
              have h4 := mul_le_mul_of_nonneg_left hb hKpos.le
              rw [key] at h4
              rw [hA]
              linarith only [h3, h4]
            have pairing : ∀ (T : ℕ) (x : Fin T → MultiDim.Cov q p), MultiDim.Admissible S x →
                ∀ k : ℕ, ∀ A : Finset (Fin T), A.card = 2 * k → ∃ f : Fin T → Fin T,
                  (∀ t ∈ A, f t ∈ A ∧ f (f t) = t ∧ f t ≠ t) ∧
                  ∑ t ∈ A, dist (x t) (x (f t)) ≤ K * ((2 * k : ℕ) : ℝ) ^ α := by
              intro T x hx k
              induction k with
              | zero =>
                intro A hA
                have : A = ∅ := Finset.card_eq_zero.1 (by simpa using hA)
                subst this
                refine ⟨id, by simp, ?_⟩
                simp only [Finset.sum_empty, mul_zero, Nat.cast_zero]
                rw [Real.zero_rpow (by linarith only [hαhalf])]; simp
              | succ k ih =>
                intro A hA
                obtain ⟨a, ha, b, hb, hab, hd⟩ := close T x hx A (by omega)
                have hb' : b ∈ A.erase a := Finset.mem_erase.2 ⟨hab.symm, hb⟩
                have hA' : ((A.erase a).erase b).card = 2 * k := by
                  rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]; omega
                obtain ⟨f', hf', hsum'⟩ := ih _ hA'
                have hmem : ∀ t, t ∈ (A.erase a).erase b ↔ t ≠ b ∧ t ≠ a ∧ t ∈ A := by
                  intro t; simp [Finset.mem_erase]
                refine ⟨fun t => if t = a then b else if t = b then a else f' t, ?_, ?_⟩
                · intro t ht
                  by_cases hta : t = a
                  · subst hta; simp [hab.symm, hab, hb]
                  by_cases htb : t = b
                  · subst htb; simp [hab, ha, hab.symm]
                  have ht' : t ∈ (A.erase a).erase b := (hmem t).2 ⟨htb, hta, ht⟩
                  obtain ⟨h1, h2, h3⟩ := hf' t ht'
                  obtain ⟨h1b, h1a, h1A⟩ := (hmem _).1 h1
                  simp [hta, htb, h1b, h1a, h1A, h2, h3]
                · rw [← Finset.add_sum_erase A _ ha, ← Finset.add_sum_erase _ _ hb']
                  have hrest : ∑ t ∈ (A.erase a).erase b,
                      dist (x t) (x (if t = a then b else if t = b then a else f' t)) =
                      ∑ t ∈ (A.erase a).erase b, dist (x t) (x (f' t)) := by
                    refine Finset.sum_congr rfl fun t ht => ?_
                    obtain ⟨h1, h2, _⟩ := (hmem t).1 ht
                    simp [h1, h2]
                  dsimp only
                  rw [hrest, if_pos rfl, if_neg (Ne.symm hab), if_pos rfl, dist_comm (x b) (x a)]
                  rw [hA] at hd
                  have hn : (2:ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) := by push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
                  have hst := step _ hn
                  have hk2 : ((2 * k : ℕ) : ℝ) = ((2 * (k + 1) : ℕ) : ℝ) - 2 := by push_cast; ring
                  rw [hk2] at hsum'
                  linarith only [hd, hsum', hst]
            have upper : ∀ T : ℕ, Even T → ∀ x : Fin T → MultiDim.Cov q p, MultiDim.Admissible S x →
                ∃ w : {w : Fin T → Bool // (Finset.univ.filter (fun t => w t = false)).card = T / 2},
                  PigeonholeDesign.Upper.discrepancy x w.1 ≤ K * (T:ℝ) ^ α := by
              intro T hT x hx
              obtain ⟨k, hk⟩ := hT
              obtain ⟨f, hf, hsum⟩ := pairing T x hx k Finset.univ (by simp; omega)
              simp only [Finset.mem_univ, true_implies, forall_const] at hf
              let w : Fin T → Bool := fun t => decide (t < f t)
              have hwf : ∀ t, w t = false → w (f t) = true := by
                intro t ht
                simp only [w, decide_eq_false_iff_not, not_lt, decide_eq_true_eq] at ht ⊢
                rw [(hf t).2.1]
                exact lt_of_le_of_ne ht (hf t).2.2
              have hwt : ∀ t, w t = true → w (f t) = false := by
                intro t ht
                simp only [w, decide_eq_false_iff_not, not_lt, decide_eq_true_eq] at ht ⊢
                rw [(hf t).2.1]
                exact ht.le
              let e : {t // w t = false} ≃ {t // w t = true} :=
                ⟨fun a => ⟨f a, hwf a a.2⟩, fun b => ⟨f b, hwt b b.2⟩,
                  fun a => Subtype.ext ((hf a).2.1), fun b => Subtype.ext ((hf b).2.1)⟩
              have hcard : (Finset.univ.filter (fun t => w t = false)).card = T / 2 := by
                have h1 := Fintype.card_congr e
                rw [Fintype.card_subtype, Fintype.card_subtype] at h1
                have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
                  (fun t => w t = false)
                simp only [Bool.not_eq_false, Finset.card_univ, Fintype.card_fin] at h2
                omega
              refine ⟨⟨w, hcard⟩, ?_⟩
              calc PigeonholeDesign.Upper.discrepancy x w
                  ≤ ∑ a : {t // w t = false}, dist (x a) (x (e a)) :=
                    ciInf_le (Set.finite_range _).bddBelow e
                _ = ∑ t ∈ Finset.univ.filter (fun t => w t = false), dist (x t) (x (f t)) :=
                    (Finset.sum_subtype _ (by simp) (fun t => dist (x t) (x (f t)))).symm
                _ ≤ ∑ t, dist (x t) (x (f t)) :=
                    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                      (fun _ _ _ => dist_nonneg)
                _ ≤ K * (T:ℝ) ^ α := by
                    convert hsum using 3; push_cast; rw [hk]; push_cast; ring
            refine ⟨1/4, K, by norm_num, hKpos, 1, fun T hT1 hTe => ⟨?_, ?_⟩⟩
            · intro x hx
              obtain ⟨w, hw⟩ := upper T hTe x hx
              calc mpdDisc x ≤ PigeonholeDesign.Upper.discrepancy x w.1 :=
                    ciInf_le (Set.finite_range _).bddBelow w
                _ ≤ _ := hw
            · have hT0 : (0:ℝ) < T := by exact_mod_cast hT1
              set r : ℝ := (T:ℝ) ^ ((p:ℝ)⁻¹) with hr_def
              have hr1 : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast hT1) (by positivity)
              have hrp : r ^ p = T := Real.rpow_inv_natCast_pow hT0.le (by omega)
              set m := ⌈r⌉₊ with hm
              have hm1 : r ≤ m := Nat.le_ceil r
              have hm2 : (m:ℝ) < r + 1 := Nat.ceil_lt_add_one (by linarith only [hr1])
              have hmpos : (0:ℝ) < m := by linarith only [hr1, hm1]
              have hTm : T ≤ Fintype.card (Fin p → Fin m) := by
                rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
                have : (T:ℝ) ≤ (m:ℝ) ^ p := by rw [← hrp]; exact pow_le_pow_left₀ (by linarith only [hr1]) hm1 p
                exact_mod_cast this
              let g : Fin T → (Fin p → Fin m) := fun t => (Fintype.equivFin _).symm (Fin.castLE hTm t)
              have hg : Function.Injective g :=
                (Fintype.equivFin _).symm.injective.comp (Fin.castLE_injective hTm)
              let s : Fin q → ℝ := fun i => (hne i).choose
              let x : Fin T → MultiDim.Cov q p :=
                fun t => WithLp.toLp 2 (Sum.elim s (fun j => ((g t j : ℕ) : ℝ) / m))
              have hxa : MultiDim.Admissible S x := by
                refine ⟨fun t i => (hne i).choose_spec, fun t j => ?_⟩
                simp only [x, PiLp.toLp_apply, Sum.elim_inr]
                constructor
                · positivity
                · rw [div_le_one hmpos]; exact_mod_cast (g t j).isLt.le
              have hsep : ∀ t t', t ≠ t' → 1 / (m:ℝ) ≤ dist (x t) (x t') := by
                intro t t' htt
                obtain ⟨j, hj⟩ : ∃ j, g t j ≠ g t' j := by
                  by_contra hcon; push_neg at hcon; exact htt (hg (funext hcon))
                refine le_trans ?_ (PiLp.dist_apply_le _ _ (Sum.inr j))
                simp only [x, PiLp.toLp_apply, Sum.elim_inr, Real.dist_eq]
                rw [← sub_div, abs_div, abs_of_pos hmpos]
                gcongr
                rw [le_abs]
                rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with h | h
                · right
                  have : ((g t j : ℕ) : ℝ) + 1 ≤ (g t' j : ℕ) := by exact_mod_cast h
                  linarith only [this]
                · left
                  have : ((g t' j : ℕ) : ℝ) + 1 ≤ (g t j : ℕ) := by exact_mod_cast h
                  linarith only [this]
              refine ⟨x, hxa, ?_⟩
              obtain ⟨w0, _⟩ := upper T hTe x hxa
              haveI : Nonempty {w : Fin T → Bool //
                (Finset.univ.filter (fun t => w t = false)).card = T / 2} := ⟨w0⟩
              obtain ⟨k, hk⟩ := hTe
              have hlow : ((T / 2 : ℕ) : ℝ) * (1 / m) ≤ mpdDisc x := by
                unfold mpdDisc
                refine le_ciInf fun w => ?_
                have hc1 : Fintype.card {t // w.1 t = false} = T / 2 := by
                  rw [Fintype.card_subtype]; exact w.2
                have hc2 : Fintype.card {t // w.1 t = true} = T / 2 := by
                  rw [Fintype.card_subtype]
                  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
                    (fun t => w.1 t = false)
                  simp only [Bool.not_eq_false, Finset.card_univ, Fintype.card_fin] at h2
                  have := w.2; omega
                haveI : Nonempty ({t // w.1 t = false} ≃ {t // w.1 t = true}) :=
                  ⟨Fintype.equivOfCardEq (hc1.trans hc2.symm)⟩
                unfold PigeonholeDesign.Upper.discrepancy
                refine le_ciInf fun e => ?_
                calc ((T / 2 : ℕ) : ℝ) * (1 / m) = ∑ _a : {t // w.1 t = false}, 1 / (m:ℝ) := by
                      simp [hc1]
                  _ ≤ _ := Finset.sum_le_sum fun a _ => hsep _ _ (fun h => by
                      have h1 := (e a).2
                      rw [← h, a.2] at h1
                      exact Bool.false_ne_true h1)
              have hTa : (T:ℝ) ^ α = T / r := by rw [eq_div_iff (by positivity)]; exact hsplit _ hT0
              have hk2 : T / 2 = k := by omega
              rw [hk2] at hlow
              have hkR : (T:ℝ) = 2 * k := by norm_cast; omega
              refine le_trans ?_ hlow
              rw [hTa, hkR]
              have h1 : 1 / (2 * r) ≤ 1 / (m:ℝ) := one_div_le_one_div_of_le hmpos (by linarith only [hm2, hr1])
              calc 1 / 4 * (2 * (k:ℝ) / r) = k * (1 / (2 * r)) := by field_simp; ring
                _ ≤ k * (1 / m) := by gcongr
