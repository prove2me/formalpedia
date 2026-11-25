-- Prove2me | solution 1 for PigeonholeDesign.Upper.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T03:12:29.901813+00:00
-- url     : https://prove2.me/submissions/a7772e5f-7026-433b-9739-4416306870d6

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

namespace PigeonholeDesign.Upper.Supplement

lemma gen_le {E : Type*} [PseudoMetricSpace E] (m : ℕ) (x : Fin (m + m) → E) (r : Fin (m + m) → ℕ)
    (R : ℕ) (hr : ∀ t, r t ≤ R) (hrx : ∀ a b, r a = r b → x a = x b) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ a b, dist (x a) (x b) ≤ D) : mpdDisc x ≤ D * R := by
  set s := Tuple.sort r with hs
  have hmono : Monotone (r ∘ s) := Tuple.monotone_sort r
  let φ : Fin m × Fin 2 ≃ Fin (m + m) :=
    (finProdFinEquiv.trans (finCongr (by omega : m * 2 = m + m))).trans s
  have hφ : ∀ k : Fin m, ∀ j : Fin 2, φ (k, j) = s ⟨j + 2 * k, by omega⟩ := by
    intro k j; simp [φ, finProdFinEquiv]
  let w : Fin (m + m) → Bool := fun t => decide ((φ.symm t).2 = 1)
  let A : Fin m ≃ {t // w t = false} :=
    { toFun := fun k => ⟨φ (k, 0), by simp [w]⟩
      invFun := fun t => (φ.symm t.1).1
      left_inv := fun k => by simp
      right_inv := fun t => by
        obtain ⟨t, ht⟩ := t
        have h2 : (φ.symm t).2 = 0 := by
          have : ¬ (φ.symm t).2 = 1 := by simpa [w] using ht
          omega
        apply Subtype.ext
        simp only
        conv_rhs => rw [← φ.apply_symm_apply t]
        rw [← h2] }
  let B : Fin m ≃ {t // w t = true} :=
    { toFun := fun k => ⟨φ (k, 1), by simp [w]⟩
      invFun := fun t => (φ.symm t.1).1
      left_inv := fun k => by simp
      right_inv := fun t => by
        obtain ⟨t, ht⟩ := t
        have h2 : (φ.symm t).2 = 1 := by simpa [w] using ht
        apply Subtype.ext
        simp only
        conv_rhs => rw [← φ.apply_symm_apply t]
        rw [← h2] }
  have hcard : (Finset.univ.filter (fun t => w t = false)).card = (m + m) / 2 := by
    rw [← Fintype.card_subtype, ← Fintype.card_congr A]; simp; omega
  have hnn : ∀ w' : Fin (m + m) → Bool, 0 ≤ PigeonholeDesign.Upper.discrepancy x w' := fun w' =>
    Real.iInf_nonneg (fun e => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  have h1 : mpdDisc x ≤ PigeonholeDesign.Upper.discrepancy x w := by
    unfold mpdDisc
    exact ciInf_le ⟨0, by rintro _ ⟨w', rfl⟩; exact hnn w'.1⟩ (⟨w, hcard⟩ :
      {w : Fin (m + m) → Bool // (Finset.univ.filter (fun t => w t = false)).card = (m + m) / 2})
  let e : {t // w t = false} ≃ {t // w t = true} := A.symm.trans B
  have h2 : PigeonholeDesign.Upper.discrepancy x w ≤
      ∑ a : {t // w t = false}, dist (x a) (x (e a)) := by
    unfold PigeonholeDesign.Upper.discrepancy
    exact ciInf_le ⟨0, by rintro _ ⟨e', rfl⟩; exact Finset.sum_nonneg (fun _ _ => dist_nonneg)⟩ e
  let f : ℕ → ℝ := fun n => if h : n < m + m then (r (s ⟨n, h⟩) : ℝ) else R
  have fmono : Monotone f := by
    intro a b hab
    simp only [f]
    split_ifs with ha hb hb
    · exact_mod_cast hmono (show (⟨a, ha⟩ : Fin (m+m)) ≤ ⟨b, hb⟩ from hab)
    · exact_mod_cast hr _
    · omega
    · exact le_rfl
  have h3 : ∑ a : {t // w t = false}, dist (x a) (x (e a)) ≤
      ∑ k ∈ Finset.range m, D * (f (2 * k + 1) - f (2 * k)) := by
    rw [← Equiv.sum_comp A, ← Fin.sum_univ_eq_sum_range (fun k => D * (f (2 * k + 1) - f (2 * k)))]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have he : e (A k) = B k := by simp [e]
    rw [he]
    show dist (x (φ (k, 0))) (x (φ (k, 1))) ≤ _
    rw [hφ, hφ]
    have hk1 : 2 * (k : ℕ) + 1 < m + m := by omega
    have hk0 : 2 * (k : ℕ) < m + m := by omega
    have e0 : (⟨((0 : Fin 2) : ℕ) + 2 * k, by omega⟩ : Fin (m+m)) = ⟨2 * k, hk0⟩ := by ext; simp
    have e1 : (⟨((1 : Fin 2) : ℕ) + 2 * k, by omega⟩ : Fin (m+m)) = ⟨2 * k + 1, hk1⟩ := by
      ext; simp; omega
    rw [e0, e1]
    simp only [f, dif_pos hk1, dif_pos hk0]
    have hle : r (s ⟨2 * k, hk0⟩) ≤ r (s ⟨2 * k + 1, hk1⟩) :=
      hmono (show (⟨2 * k, hk0⟩ : Fin (m+m)) ≤ ⟨2 * k + 1, hk1⟩ from by simp [Fin.le_def])
    by_cases heq : r (s ⟨2 * k, hk0⟩) = r (s ⟨2 * k + 1, hk1⟩)
    · rw [hrx _ _ heq, dist_self, heq, sub_self, mul_zero]
    · have hlt : (r (s ⟨2 * k, hk0⟩) : ℝ) + 1 ≤ r (s ⟨2 * k + 1, hk1⟩) := by
        exact_mod_cast (show r (s ⟨2 * k, hk0⟩) + 1 ≤ r (s ⟨2 * k + 1, hk1⟩) by omega)
      calc dist _ _ ≤ D := hD _ _
        _ ≤ _ := le_mul_of_one_le_right hD0 (by linarith)
  have h4 : ∑ k ∈ Finset.range m, D * (f (2 * k + 1) - f (2 * k)) ≤
      ∑ k ∈ Finset.range m, D * (f (2 * (k + 1)) - f (2 * k)) :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (by
      have := fmono (show 2 * k + 1 ≤ 2 * (k + 1) by omega); linarith) hD0)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub (fun k => f (2 * k))] at h4
  rw [← Finset.mul_sum] at h3
  have hfm : f (2 * m) = R := by simp only [f]; rw [dif_neg (by omega)]
  have hf0 : 0 ≤ f 0 := by
    simp only [f]; split_ifs
    · positivity
    · positivity
  simp only [mul_zero] at h4
  rw [hfm] at h4
  have : D * ((R:ℝ) - f 0) ≤ D * R := mul_le_mul_of_nonneg_left (by linarith) hD0
  linarith

open PigeonholeDesign.MultiDim in
theorem theorem_1 (q : ℕ) (hq : 1 ≤ q) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty)
    (h2 : ∃ i, 2 ≤ (S i).card) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      (∀ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x → mpdDisc x ≤ C) ∧
      (∃ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x ∧ c ≤ mpdDisc x) := by
  obtain ⟨i0, hi0⟩ := h2
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (S i0).card)
  choose z hz using hne
  let mk : ℝ → Cov q 0 := fun v => WithLp.toLp 2 (fun j => match j with
    | Sum.inl i => if i = i0 then v else z i
    | Sum.inr j => j.elim0)
  have mk_apply : ∀ v i, mk v (Sum.inl i) = if i = i0 then v else z i := fun v i => by
    simp [mk]
  clear_value mk
  let c := dist (mk a) (mk b)
  have hc : 0 < c := by
    apply dist_pos.mpr
    intro h
    have := congrArg (fun p : Cov q 0 => p (Sum.inl i0)) h
    simp only [mk_apply] at this; simp at this
    exact hab this
  obtain ⟨K, hK⟩ : ∃ K, K = ∏ i, (S i).card := ⟨_, rfl⟩
  refine ⟨c, Real.sqrt q * K + 1, hc, add_pos_of_nonneg_of_pos (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) one_pos, 2, fun T hT2 hT => ⟨?_, ?_⟩⟩
  · intro x hx
    obtain ⟨m, rfl⟩ := hT
    let key : Cov q 0 → (Fin q → ℝ) := fun p i => p (Sum.inl i)
    let P := Fintype.piFinset S
    have hmem : ∀ t, key (x t) ∈ P := fun t => Fintype.mem_piFinset.mpr (fun i => hx.1 t i)
    let r : Fin (m + m) → ℕ := fun t => (P.equivFin ⟨key (x t), hmem t⟩ : ℕ)
    have hPK : P.card = K := by rw [hK]; exact Fintype.card_piFinset S
    have hr : ∀ t, r t ≤ K := fun t => by
      have := (P.equivFin ⟨key (x t), hmem t⟩).isLt; simp only [r]; omega
    have hrx : ∀ a b, r a = r b → x a = x b := by
      intro a b h
      have h' := P.equivFin.injective (Fin.ext h)
      have hk : key (x a) = key (x b) := congrArg Subtype.val h'
      ext j
      rcases j with i | j
      · exact congrFun hk i
      · exact j.elim0
    have hD : ∀ a b, dist (x a) (x b) ≤ Real.sqrt q := by
      intro a b
      rw [EuclideanSpace.dist_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, dist (x a i) (x b i) ^ 2 ≤ ∑ _i : Fin q ⊕ Fin 0, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j _
            rcases j with i | j
            · have h1 := hS i (hx.1 a i); have h2 := hS i (hx.1 b i)
              simp only [Set.mem_Icc] at h1 h2
              rw [Real.dist_eq]
              have : |x a (Sum.inl i) - x b (Sum.inl i)| ≤ 1 := by
                rw [abs_le]; constructor <;> linarith
              have h0 := abs_nonneg (x a (Sum.inl i) - x b (Sum.inl i))
              nlinarith
            · exact j.elim0
        _ = q := by simp
    have := gen_le m x r K hr hrx (Real.sqrt q) (Real.sqrt_nonneg _) hD
    linarith
  · have hTpos : 0 < T := by omega
    let x : Fin T → Cov q 0 := fun t => if (t : ℕ) = 0 then mk a else mk b
    refine ⟨x, ⟨fun t i => ?_, fun t j => j.elim0⟩, ?_⟩
    · simp only [x]
      split_ifs <;> rw [mk_apply] <;> split_ifs with h <;> (try subst h) <;> first | exact ha | exact hb | exact hz i
    · unfold mpdDisc
      have hne' : Nonempty {w : Fin T → Bool // (Finset.univ.filter (fun t => w t = false)).card = T / 2} := by
        refine ⟨⟨fun t => decide (T / 2 ≤ (t : ℕ)), ?_⟩⟩
        have : (Finset.univ.filter (fun t : Fin T => decide (T / 2 ≤ (t : ℕ)) = false)) =
            (Finset.univ : Finset (Fin (T / 2))).map (Fin.castLEEmb (by omega)) := by
          ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Fin.castLEEmb_apply, decide_eq_false_iff_not, not_le]
          constructor
          · intro h; exact ⟨⟨t, h⟩, by ext; simp⟩
          · rintro ⟨u, rfl⟩; simp
        rw [this, Finset.card_map]; simp
      apply le_ciInf
      rintro ⟨w, hw⟩
      unfold PigeonholeDesign.Upper.discrepancy
      have hcf : Fintype.card {t // w t = false} = T / 2 := by rw [Fintype.card_subtype]; exact hw
      have hct : Fintype.card {t // w t = true} = T / 2 := by
        have h3 : Fintype.card {t // w t = true} = Fintype.card {t // ¬ (w t = false)} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun t => by simp))
        rw [h3, Fintype.card_subtype_compl, hcf, Fintype.card_fin]; obtain ⟨k, rfl⟩ := hT; omega
      have : Nonempty ({t // w t = false} ≃ {t // w t = true}) :=
        ⟨Fintype.equivOfCardEq (hcf.trans hct.symm)⟩
      apply le_ciInf
      intro e
      have hnn : ∀ i ∈ (Finset.univ : Finset {t // w t = false}), 0 ≤ dist (x i) (x (e i)) :=
        fun _ _ => dist_nonneg
      let t0 : Fin T := ⟨0, hTpos⟩
      cases h0 : w t0
      · let a0 : {t // w t = false} := ⟨t0, h0⟩
        have hne0 : ((e a0 : Fin T) : ℕ) ≠ 0 := by
          intro h
          have h1 : w (e a0 : Fin T) = true := (e a0).2
          have : (e a0 : Fin T) = t0 := Fin.ext h
          rw [this, h0] at h1; exact Bool.false_ne_true h1
        calc c = dist (x a0) (x (e a0)) := by simp [x, a0, t0, hne0, c]
          _ ≤ _ := Finset.single_le_sum hnn (Finset.mem_univ a0)
      · let b0 : {t // w t = true} := ⟨t0, h0⟩
        have hne0 : ((e.symm b0 : Fin T) : ℕ) ≠ 0 := by
          intro h
          have h1 : w (e.symm b0 : Fin T) = false := (e.symm b0).2
          have : (e.symm b0 : Fin T) = t0 := Fin.ext h
          rw [this, h0] at h1; exact Bool.false_ne_true h1.symm
        calc c = dist (x (e.symm b0)) (x (e (e.symm b0))) := by
              rw [Equiv.apply_symm_apply]; simp [x, b0, t0, hne0, c, dist_comm]
          _ ≤ _ := Finset.single_le_sum hnn (Finset.mem_univ _)

end PigeonholeDesign.Upper.Supplement

open PigeonholeDesign.Upper.Supplement in
theorem solution (q : ℕ) (hq : 1 ≤ q) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty)
    (h2 : ∃ i, 2 ≤ (S i).card) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      (∀ x : Fin T → PigeonholeDesign.MultiDim.Cov q 0, PigeonholeDesign.MultiDim.Admissible S x → mpdDisc x ≤ C) ∧
      (∃ x : Fin T → PigeonholeDesign.MultiDim.Cov q 0, PigeonholeDesign.MultiDim.Admissible S x ∧ c ≤ mpdDisc x) :=
  PigeonholeDesign.Upper.Supplement.theorem_1 q hq S hS hne h2
