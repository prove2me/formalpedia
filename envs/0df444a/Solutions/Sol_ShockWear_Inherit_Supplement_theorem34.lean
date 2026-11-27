-- Prove2me | solution 1 for ShockWear.Inherit.Supplement.theorem34
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:55.144537+00:00
-- url     : https://prove2.me/submissions/6cc021be-25a8-479e-b2b3-ba0f6ece1936

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_TotalPositivity

open ShockWear
open ShockWear.Inherit
open ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (n : ℕ) (hn : 1 ≤ n) (eps : ℝ) (heps : eps = 1 ∨ eps = -1) :
    (IsSC n eps Set.univ Set.univ (fun j k : ℕ => failProb P (j + k + 1)) →
      IsSC n eps (Set.Ioi 0) (Set.Ioi 0) (fun s t : ℝ => shockDens lam P (s + t))) ∧
    (IsSC n eps Set.univ Set.univ (fun j k : ℕ => P (j + k)) →
      IsSC n eps (Set.Ioi 0) (Set.Ioi 0)
        (fun s t : ℝ => ShockWear.CumDamage.shockSurv lam P (s + t))) := by
          have CB : ∀ (n N : ℕ) (F : Fin n → ℕ → ℝ) (G : ℕ → Fin n → ℝ) (e1 e2 : ℝ),
              (∀ m : Fin n → ℕ, StrictMono m → 0 ≤ e1 * (Matrix.of fun p r => F p (m r)).det) →
              (∀ m : Fin n → ℕ, StrictMono m → 0 ≤ e2 * (Matrix.of fun r q => G (m r) q).det) →
              0 ≤ e1 * e2 * (Matrix.of fun p q => ∑ k ∈ Finset.range N, F p k * G k q).det := by
              intro n N F G e1 e2 hF hG
              classical
              -- expansion
              have hexp : (Matrix.of fun p q => ∑ k ∈ Finset.range N, F p k * G k q).det
                  = ∑ r : Fin n → Fin N, (∏ p, F p (r p)) * (Matrix.of fun p q => G (r p) q).det := by
                have h1 : (Matrix.of fun p q => ∑ k ∈ Finset.range N, F p k * G k q)
                    = fun p => ∑ k : Fin N, F p k • (fun q => G k q) := by
                  ext p q
                  simp only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
                  rw [Fin.sum_univ_eq_sum_range (fun k => F p k * G k q)]
                rw [h1]
                change (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap _ = _
                rw [MultilinearMap.map_sum]
                refine Finset.sum_congr rfl fun r _ => ?_
                rw [← Matrix.det_mul_column]
                rfl
              set a : (Fin n → Fin N) → ℝ := fun r => (∏ p, F p (r p)) * (Matrix.of fun p q => G (r p) q).det
                with ha
              set T : (Fin n → Fin N) → ℝ := fun r =>
                (Matrix.of fun p q => F p (r q)).det * (Matrix.of fun p q => G (r p) q).det with hT
              have hsym : ∀ σ : Equiv.Perm (Fin n), ∑ r, a r = ∑ r, a (r ∘ σ) := by
                intro σ
                exact (Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ (fun r => rfl)).symm
              have hsum : (Nat.factorial n : ℝ) * ∑ r, a r = ∑ r, T r := by
                have : (Nat.factorial n : ℝ) * ∑ r, a r = ∑ σ : Equiv.Perm (Fin n), ∑ r, a (r ∘ σ) := by
                  rw [Finset.sum_congr rfl (fun σ _ => (hsym σ).symm), Finset.sum_const, Finset.card_univ,
                    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
                rw [this, Finset.sum_comm]
                refine Finset.sum_congr rfl fun r _ => ?_
                have h2 : ∀ σ : Equiv.Perm (Fin n), a (r ∘ σ) =
                    ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ p, F p (r (σ p))) * (Matrix.of fun p q => G (r p) q).det := by
                  intro σ
                  simp only [ha, Function.comp_apply]
                  have := Matrix.det_permute σ (Matrix.of fun p q => G (r p) q)
                  rw [show (Matrix.of fun p q => G (r (σ p)) q) = (Matrix.of fun p q => G (r p) q).submatrix σ id
                    from by ext; simp, this]
                  push_cast; ring
                simp only [h2, hT]
                rw [← Finset.sum_mul]
                congr 1
                rw [← Matrix.det_transpose, Matrix.det_apply']
                refine Finset.sum_congr rfl fun σ _ => ?_
                simp [Matrix.transpose_apply, Units.smul_def]
              have hT0 : ∀ r, 0 ≤ e1 * e2 * T r := by
                intro r
                by_cases hinj : Function.Injective r
                · set σ := Tuple.sort r
                  have hmono : StrictMono (r ∘ σ) :=
                    (Tuple.monotone_sort r).strictMono_of_injective (hinj.comp σ.injective)
                  have hTe : T r = T (r ∘ σ) := by
                    simp only [hT, Function.comp_apply]
                    rw [show (Matrix.of fun p q => F p (r (σ q))) = (Matrix.of fun p q => F p (r q)).submatrix id σ
                      from by ext; simp, Matrix.det_permute',
                      show (Matrix.of fun p q => G (r (σ p)) q) = (Matrix.of fun p q => G (r p) q).submatrix σ id
                      from by ext; simp, Matrix.det_permute]
                    have : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
                      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
                    linear_combination (-(Matrix.of fun p q => F p (r q)).det * (Matrix.of fun p q => G (r p) q).det) * this
                  have hm : StrictMono (fun i => ((r ∘ σ) i : ℕ)) := Fin.val_strictMono.comp hmono
                  have h1 := hF _ hm
                  have h2 := hG _ hm
                  rw [hTe]
                  simp only [hT]
                  nlinarith [mul_nonneg h1 h2]
                · simp only [Function.Injective, not_forall] at hinj
                  obtain ⟨i, j, hij, hne⟩ := hinj
                  have : (Matrix.of fun p q => G (r p) q).det = 0 :=
                    Matrix.det_zero_of_row_eq hne (by ext q; simp [hij])
                  simp [hT, this]
              have hpos : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
              rw [hexp]
              have : 0 ≤ (Nat.factorial n : ℝ) * (e1 * e2 * ∑ r, a r) := by
                rw [show (Nat.factorial n : ℝ) * (e1 * e2 * ∑ r, a r) = e1 * e2 * ((Nat.factorial n : ℝ) * ∑ r, a r) by ring,
                  hsum, Finset.mul_sum]
                exact Finset.sum_nonneg fun r _ => hT0 r
              exact (mul_nonneg_iff_of_pos_left hpos).mp this
          -- generalized Vandermonde
          have GV : ∀ (x : Fin n → ℝ), (∀ i, 0 < x i) → StrictMono x → ∀ e : Fin n → ℕ, StrictMono e →
              0 ≤ (Matrix.of fun p q => x p ^ e q).det := by
            have Z : ∀ m : ℕ, ∀ (e : Fin m → ℕ), StrictMono e → ∀ (c : Fin m → ℝ) (x : Fin m → ℝ),
                (∀ i, 0 < x i) → StrictMono x → (∀ p, ∑ q, c q * x p ^ e q = 0) → ∀ q, c q = 0 := by
              intro m
              induction m with
              | zero => intro e _ c x _ _ _ q; exact q.elim0
              | succ m ih =>
                intro e he c x hx hxm hz
                have he0 : ∀ q, e 0 ≤ e q := fun q => he.monotone (Fin.zero_le q)
                set g : ℝ → ℝ := fun t => ∑ q, c q * t ^ (e q - e 0) with hgdef
                have hg : ∀ p, g (x p) = 0 := by
                  intro p
                  have h := hz p
                  have : ∑ q, c q * x p ^ e q = x p ^ e 0 * g (x p) := by
                    simp only [g, Finset.mul_sum]
                    refine Finset.sum_congr rfl fun q _ => ?_
                    rw [show e q = e 0 + (e q - e 0) by have := he0 q; omega, pow_add]
                    simp only [Nat.add_sub_cancel_left]
                    ring
                  rw [this] at h
                  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hx p).ne')
                set g' : ℝ → ℝ := fun t => ∑ q, c q * (((e q - e 0 : ℕ) : ℝ) * t ^ (e q - e 0 - 1)) with hg'def
                have hd : ∀ t, HasDerivAt g (g' t) t := by
                  intro t
                  exact HasDerivAt.fun_sum (u := Finset.univ)
                    (fun q _ => (hasDerivAt_pow (e q - e 0) t).const_mul (c q))
                have hr : ∀ i : Fin m, ∃ y ∈ Set.Ioo (x i.castSucc) (x i.succ), g' y = 0 := by
                  intro i
                  exact exists_hasDerivAt_eq_zero (hxm (Fin.castSucc_lt_succ (i := i)))
                    (fun t _ => (hd t).continuousAt.continuousWithinAt) (by rw [hg, hg]) (fun t _ => hd t)
                choose y hy hy0 using hr
                have hym : StrictMono y := by
                  intro i j hij
                  have h1 : x i.succ ≤ x j.castSucc := hxm.monotone (by rw [Fin.le_def]; simp; omega)
                  linarith [(hy i).2, (hy j).1]
                have hypos : ∀ i, 0 < y i := fun i => (hx i.castSucc).trans (hy i).1
                have hsucc := ih (fun q => e q.succ - e 0 - 1)
                  (fun i j hij => by
                    have h1 := he (Fin.succ_lt_succ_iff.mpr hij)
                    have h2 := he (Fin.succ_pos i)
                    simp only; omega)
                  (fun q => c q.succ * ((e q.succ - e 0 : ℕ) : ℝ)) y hypos hym (fun p => by
                    have := hy0 p
                    simp only [g', Fin.sum_univ_succ, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero,
                      zero_add] at this
                    rw [← this]
                    refine Finset.sum_congr rfl fun q _ => by ring)
                have hs : ∀ r : Fin m, c r.succ = 0 := by
                  intro r
                  have h := hsucc r
                  have h2 := he (Fin.succ_pos r)
                  have : ((e r.succ - e 0 : ℕ) : ℝ) ≠ 0 := by
                    rw [Nat.cast_ne_zero]; omega
                  exact (mul_eq_zero.mp h).resolve_right this
                have h0 : c 0 = 0 := by
                  have h := hz 0
                  simp only [Fin.sum_univ_succ, hs, zero_mul, Finset.sum_const_zero, add_zero] at h
                  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (hx 0).ne')
                intro q
                refine Fin.cases h0 hs q
            have GV' : ∀ m : ℕ, ∀ (x : Fin m → ℝ), (∀ i, 0 < x i) → StrictMono x → ∀ e : Fin m → ℕ,
                StrictMono e → 0 < (Matrix.of fun p q => x p ^ e q).det := by
              intro m
              induction m with
              | zero => intros; simp
              | succ m ih =>
                intro x hx hxm e he
                set c : Fin (m+1) → ℝ := fun q => (-1) ^ ((Fin.last m : ℕ) + (q : ℕ)) *
                  ((Matrix.of fun p q => x p ^ e q).submatrix (Fin.last m).succAbove q.succAbove).det with hc
                have hD : ∀ t, (Matrix.updateRow (Matrix.of fun p q => x p ^ e q) (Fin.last m)
                    (fun q => t ^ e q)).det = ∑ q, c q * t ^ e q := by
                  intro t
                  rw [Matrix.det_succ_row _ (Fin.last m)]
                  refine Finset.sum_congr rfl fun q _ => ?_
                  rw [Matrix.submatrix_updateRow_succAbove]
                  simp only [c, Matrix.updateRow_self]
                  ring
                have hclast : 0 < c (Fin.last m) := by
                  simp only [c, Fin.succAbove_last]
                  rw [← two_mul, pow_mul]
                  simp only [neg_one_sq, one_pow, one_mul]
                  exact ih (fun p => x p.castSucc) (fun i => hx _)
                    (fun i j h => hxm (Fin.castSucc_lt_castSucc_iff.mpr h)) (fun q => e q.castSucc)
                    (fun i j h => he (Fin.castSucc_lt_castSucc_iff.mpr h))
                have hDx : ∀ p : Fin (m+1), p ≠ Fin.last m → ∑ q, c q * x p ^ e q = 0 := by
                  intro p hp
                  rw [← hD]
                  refine Matrix.det_zero_of_row_eq hp ?_
                  ext q
                  simp [Matrix.updateRow_ne hp]
                have hDlast : (Matrix.of fun p q => x p ^ e q).det = ∑ q, c q * x (Fin.last m) ^ e q := by
                  have := hD (x (Fin.last m))
                  rwa [show (fun q => x (Fin.last m) ^ e q) = (Matrix.of fun p q => x p ^ e q) (Fin.last m)
                    from rfl, Matrix.updateRow_eq_self] at this
                have hno : ∀ s, x (Fin.last m) ≤ s → ∑ q, c q * s ^ e q ≠ 0 := by
                  intro s hs h0
                  set z : Fin (m+1) → ℝ := fun p => if p = Fin.last m then s else x p with hz
                  have hzpos : ∀ i, 0 < z i := by
                    intro i; by_cases hi : i = Fin.last m
                    · simp only [z, hi, if_true]; linarith [hx (Fin.last m)]
                    · simp only [z, hi, if_false]; exact hx i
                  have hzm : StrictMono z := by
                    intro i j hij
                    have hi : i ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
                    by_cases hj : j = Fin.last m
                    · simp only [z, hi, hj, if_true, if_false]
                      have := hxm (hj ▸ hij)
                      linarith
                    · simp only [z, hi, hj, if_false]; exact hxm hij
                  have := Z (m+1) e he c z hzpos hzm (fun p => by
                    by_cases hp : p = Fin.last m
                    · simp only [z, hp, if_true]; exact h0
                    · simp only [z, hp, if_false]; exact hDx p hp)
                  exact hclast.ne' (this _)
                obtain ⟨T, hT1, hT2⟩ : ∃ T, x (Fin.last m) ≤ T ∧ 0 < ∑ q, c q * T ^ e q := by
                  set C := c (Fin.last m) with hC
                  set S := ∑ i : Fin m, |c i.castSucc| with hSdef
                  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
                  have hxl := hx (Fin.last m)
                  have hSC := div_nonneg hS hclast.le
                  refine ⟨x (Fin.last m) + 1 + S / C, by linarith, ?_⟩
                  set T := x (Fin.last m) + 1 + S / C with hTdef
                  have hT : 1 ≤ T := by linarith
                  have hCT : S < C * T := by
                    have : C * (S / C) = S := mul_div_cancel₀ _ hclast.ne'
                    nlinarith
                  have hb : ∀ i : Fin m, -(|c i.castSucc| * T ^ e (Fin.last m)) ≤
                      T * (c i.castSucc * T ^ e i.castSucc) := by
                    intro i
                    have h1 : T ^ e i.castSucc * T ≤ T ^ e (Fin.last m) := by
                      rw [← pow_succ]; exact pow_le_pow_right₀ hT (he (Fin.castSucc_lt_last i))
                    have h2 : -|c i.castSucc| ≤ c i.castSucc := neg_abs_le _
                    have h3 : 0 ≤ T ^ e i.castSucc * T := by positivity
                    nlinarith [mul_nonneg (by linarith : 0 ≤ c i.castSucc + |c i.castSucc|) h3,
                      mul_nonneg (abs_nonneg (c i.castSucc)) (sub_nonneg.2 h1)]
                  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hb i
                  rw [Fin.sum_univ_castSucc]
                  have : 0 < T * (∑ i : Fin m, c i.castSucc * T ^ e i.castSucc + C * T ^ e (Fin.last m)) := by
                    rw [mul_add, Finset.mul_sum]
                    simp only [Finset.sum_neg_distrib, ← Finset.sum_mul] at hsum
                    have hTE : 0 < T ^ e (Fin.last m) := by positivity
                    nlinarith [mul_lt_mul_of_pos_right hCT hTE]
                  exact pos_of_mul_pos_right this (by linarith)
                by_contra hneg
                push Not at hneg
                rw [hDlast] at hneg
                have hcont : ContinuousOn (fun t : ℝ => ∑ q, c q * t ^ e q) (Set.Icc (x (Fin.last m)) T) := by
                  fun_prop
                obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc hT1 hcont ⟨hneg, hT2.le⟩
                exact hno s hs.1 hs0
            exact fun x hx hxm e he => (GV' n x hx hxm e he).le
          have PW : ∀ (x : Fin n → ℝ), (∀ i, 0 < x i) → StrictMono x → ∀ e : Fin n → ℕ, StrictMono e →
              0 ≤ (Matrix.of fun p q => ShockWear.CumDamage.poisW lam (x p) (e q)).det := by
            intro x hx hxm e he
            have hx' : ∀ i, 0 < lam * x i := fun i => mul_pos hlam (hx i)
            have h := GV (fun i => lam * x i) hx' (fun i j hij => mul_lt_mul_of_pos_left (hxm hij) hlam) e he
            have h1 := Matrix.det_mul_column (fun p => Real.exp (-(lam * x p)))
              (Matrix.of fun p q => (1 / ((e q).factorial : ℝ)) * (lam * x p) ^ e q)
            have h2 := Matrix.det_mul_row (fun q => 1 / ((e q).factorial : ℝ))
              (Matrix.of fun p q => (lam * x p) ^ e q)
            simp only [Matrix.of_apply] at h1 h2
            have : (Matrix.of fun p q => ShockWear.CumDamage.poisW lam (x p) (e q))
                = Matrix.of fun p q => Real.exp (-(lam * x p)) * ((1 / ((e q).factorial : ℝ)) * (lam * x p) ^ e q) := by
              ext p q; simp [ShockWear.CumDamage.poisW]; ring
            rw [this, h1, h2]
            exact mul_nonneg (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
              (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) h)
          -- truncated kernel
          have TR : ∀ (a : ℕ → ℝ), IsSC n eps Set.univ Set.univ (fun j k : ℕ => a (j + k)) →
              ∀ x y : Fin n → ℝ, (∀ i, 0 < x i) → (∀ i, 0 < y i) → StrictMono x → StrictMono y →
              ∀ N, 0 ≤ eps * (Matrix.of fun p q => ∑ i ∈ Finset.range N,
                ShockWear.CumDamage.poisW lam (x p) i *
                  ∑ j ∈ Finset.range N, a (i + j) * ShockWear.CumDamage.poisW lam (y q) j).det := by
            intro a ha x y hx hy hxm hym N
            have := CB n N (fun p i => ShockWear.CumDamage.poisW lam (x p) i)
              (fun i q => ∑ j ∈ Finset.range N, a (i + j) * ShockWear.CumDamage.poisW lam (y q) j) 1 eps
              (fun m hm => by rw [one_mul]; exact PW x hx hxm m hm)
              (fun m hm => by
                have := CB n N (fun r j => a (m r + j)) (fun j q => ShockWear.CumDamage.poisW lam (y q) j)
                  eps 1 (fun k hk => ha m k (fun _ => trivial) (fun _ => trivial) hm hk)
                  (fun k hk => by
                    rw [one_mul, ← Matrix.det_transpose]
                    have := PW y hy hym k hk
                    convert this using 2
                    ext; simp)
                simpa using this)
            simpa using this
          -- the limit
          have GEN : ∀ (a : ℕ → ℝ), (∀ k, |a k| ≤ 1) →
              IsSC n eps Set.univ Set.univ (fun j k : ℕ => a (j + k)) →
              ∀ x y : Fin n → ℝ, (∀ i, 0 < x i) → (∀ i, 0 < y i) → StrictMono x → StrictMono y →
              0 ≤ eps * (Matrix.of fun p q =>
                ∑' k, a k * ShockWear.CumDamage.poisW lam (x p + y q) k).det := by
            intro a hab ha x y hx hy hxm hym
            have hu : ∀ z : ℝ, Summable (fun i => ShockWear.CumDamage.poisW lam z i) := by
              intro z
              have := (Real.summable_pow_div_factorial (lam * z)).mul_left (Real.exp (-(lam * z)))
              refine this.congr fun i => ?_
              simp [ShockWear.CumDamage.poisW]; ring
            have hu0 : ∀ z : ℝ, 0 < z → ∀ i, 0 ≤ ShockWear.CumDamage.poisW lam z i := by
              intro z hz i
              unfold ShockWear.CumDamage.poisW
              have : 0 < lam * z := mul_pos hlam hz
              positivity
            have anti : ∀ z w : ℝ, ∀ k : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal k,
                ShockWear.CumDamage.poisW lam z kl.1 * a (kl.1 + kl.2) * ShockWear.CumDamage.poisW lam w kl.2
                = a k * ShockWear.CumDamage.poisW lam (z + w) k := by
              intro z w k
              have e1 : ∀ kl ∈ Finset.HasAntidiagonal.antidiagonal k,
                  ShockWear.CumDamage.poisW lam z kl.1 * a (kl.1 + kl.2) * ShockWear.CumDamage.poisW lam w kl.2
                  = a k * (Real.exp (-(lam * (z + w))) / (k.factorial : ℝ)) *
                    (k.choose kl.1 • ((lam * z) ^ kl.1 * (lam * w) ^ kl.2)) := by
                intro kl hkl
                rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
                subst hkl
                unfold ShockWear.CumDamage.poisW
                rw [nsmul_eq_mul, Nat.cast_add_choose]
                have h1 : Real.exp (-(lam * (z + w))) = Real.exp (-(lam * z)) * Real.exp (-(lam * w)) := by
                  rw [← Real.exp_add]; ring_nf
                rw [h1]
                have : ((kl.1 + kl.2).factorial : ℝ) ≠ 0 := by positivity
                have : (kl.1.factorial : ℝ) ≠ 0 := by positivity
                have : (kl.2.factorial : ℝ) ≠ 0 := by positivity
                field_simp
              rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← (Commute.all _ _).add_pow']
              unfold ShockWear.CumDamage.poisW
              ring_nf
            have hlim : ∀ p q, Filter.Tendsto (fun N => ∑ i ∈ Finset.range N,
                ShockWear.CumDamage.poisW lam (x p) i *
                  ∑ j ∈ Finset.range N, a (i + j) * ShockWear.CumDamage.poisW lam (y q) j) Filter.atTop
                (nhds (∑' k, a k * ShockWear.CumDamage.poisW lam (x p + y q) k)) := by
              intro p q
              set f : ℕ × ℕ → ℝ := fun ij => ShockWear.CumDamage.poisW lam (x p) ij.1 * a (ij.1 + ij.2) *
                ShockWear.CumDamage.poisW lam (y q) ij.2 with hf
              have hsg : Summable (fun ij : ℕ × ℕ => ShockWear.CumDamage.poisW lam (x p) ij.1 *
                  ShockWear.CumDamage.poisW lam (y q) ij.2) :=
                (hu (x p)).mul_of_nonneg (hu (y q)) (hu0 _ (hx p)) (hu0 _ (hy q))
              have hfs : Summable f := by
                refine Summable.of_norm_bounded hsg fun ij => ?_
                simp only [hf, Real.norm_eq_abs, abs_mul]
                rw [abs_of_nonneg (hu0 _ (hx p) _), abs_of_nonneg (hu0 _ (hy q) _)]
                have := hab (ij.1 + ij.2)
                have h1 := hu0 _ (hx p) ij.1
                have h2 := hu0 _ (hy q) ij.2
                calc ShockWear.CumDamage.poisW lam (x p) ij.1 * |a (ij.1 + ij.2)| *
                    ShockWear.CumDamage.poisW lam (y q) ij.2
                    ≤ ShockWear.CumDamage.poisW lam (x p) ij.1 * 1 * ShockWear.CumDamage.poisW lam (y q) ij.2 := by
                      gcongr
                  _ = _ := by ring
              have hval : ∑' ij, f ij = ∑' k, a k * ShockWear.CumDamage.poisW lam (x p + y q) k := by
                rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f]
                have hs2 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff (f := f)).mpr hfs
                refine (hs2.tsum_sigma' (fun n => (hasSum_fintype _).summable)).trans ?_
                refine tsum_congr fun k => ?_
                rw [tsum_fintype, ← anti]
                exact (Finset.sum_finset_coe (fun kl => f kl) (Finset.HasAntidiagonal.antidiagonal k))
              rw [← hval]
              have := hfs.hasSum.comp (Filter.tendsto_atTop_finset_of_monotone
                (f := fun N => Finset.range N ×ˢ Finset.range N)
                (fun a b hab => Finset.product_subset_product (Finset.range_mono hab) (Finset.range_mono hab))
                (fun ij => ⟨ij.1 + ij.2 + 1, by simp <;> omega⟩))
              refine this.congr fun N => ?_
              simp only [Function.comp_apply, Finset.sum_product, hf, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
            have hdet : Filter.Tendsto (fun N => (Matrix.of fun p q => ∑ i ∈ Finset.range N,
                ShockWear.CumDamage.poisW lam (x p) i *
                  ∑ j ∈ Finset.range N, a (i + j) * ShockWear.CumDamage.poisW lam (y q) j).det) Filter.atTop
                (nhds (Matrix.of fun p q =>
                  ∑' k, a k * ShockWear.CumDamage.poisW lam (x p + y q) k).det) := by
              refine ((continuous_id.matrix_det).tendsto _).comp ?_
              exact tendsto_pi_nhds.mpr fun p => tendsto_pi_nhds.mpr fun q => hlim p q
            exact ge_of_tendsto (hdet.const_mul eps) (Filter.Eventually.of_forall fun N =>
              TR a ha x y hx hy hxm hym N)
          have hP1 : ∀ k, P k ≤ 1 := fun k => hP0 ▸ hanti (Nat.zero_le k)
          refine ⟨fun h x y hx hy hxm hym => ?_, fun h x y hx hy hxm hym => ?_⟩
          · have hb : ∀ k, |failProb P (k + 1)| ≤ 1 := by
              intro k
              have h1 := hanti (Nat.le_succ k)
              simp only [failProb]
              rw [abs_le]; constructor <;> linarith [hnn k, hnn (k+1), hP1 k]
            have := GEN (fun k => failProb P (k + 1)) hb h x y hx hy hxm hym
            have e : (Matrix.of fun i j => shockDens lam P (x i + y j)) = lam • (Matrix.of fun p q =>
                ∑' k, failProb P (k + 1) * ShockWear.CumDamage.poisW lam (x p + y q) k) := by
              ext i j; simp [shockDens]
            rw [e, Matrix.det_smul]
            have : 0 ≤ lam ^ Fintype.card (Fin n) := by positivity
            nlinarith [mul_nonneg this this]
          · have hb : ∀ k, |P k| ≤ 1 := fun k => by rw [abs_le]; constructor <;> linarith [hnn k, hP1 k]
            have := GEN P hb h x y hx hy hxm hym
            have e : (Matrix.of fun i j => ShockWear.CumDamage.shockSurv lam P (x i + y j)) = (Matrix.of fun p q =>
                ∑' k, P k * ShockWear.CumDamage.poisW lam (x p + y q) k) := by
              ext i j
              have : ¬ (x i + y j < 0) := by have := hx i; have := hy j; simp only [Set.mem_Ioi] at *; linarith
              simp [ShockWear.CumDamage.shockSurv, this]
            rw [e]; exact this
