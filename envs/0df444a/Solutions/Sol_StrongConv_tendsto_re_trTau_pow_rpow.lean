-- Prove2me | solution 1 for StrongConv.tendsto_re_trTau_pow_rpow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:32:07.102256+00:00
-- url     : https://prove2.me/submissions/b72a4517-4323-4ddb-a5c1-ee5b55630833

import Definitions.Def_StrongConv
import Mathlib

section
section
open scoped InnerProductSpace
open Matrix

noncomputable section

namespace StrongConv.Stable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (y : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    tensorOp A T y a = ∑ b, A a b • T (y b) := by
  unfold tensorOp
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.single_apply,
    PiLp.proj_apply, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_sum, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, Pi.smul_apply, Pi.single_apply]
  simp [Finset.sum_comm (γ := Fin n)]

lemma inner_tensorOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin m => H)) (y : PiLp 2 (fun _ : Fin n => H)) :
    ⟪x, tensorOp A T y⟫_ℂ = ∑ a, ∑ b, A a b * ⟪x a, T (y b)⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tensorOp_apply, inner_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_smul_right]

lemma star_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    star (tensorOp A T) = tensorOp Aᴴ (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  -- ⟪tensorOp Aᴴ T† x, y⟫ = ⟪x, tensorOp A T y⟫
  rw [inner_tensorOp, ← inner_conj_symm, inner_tensorOp, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, inner_conj_symm]
  simp only [Matrix.conjTranspose_apply, star_star, Complex.star_def]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp only [Complex.conj_conj]

end StrongConv.Stable

end
end
end

section
section
open scoped InnerProductSpace
open Matrix

noncomputable section

namespace StrongConv.Stable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensorOp_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (S T : H →L[ℂ] H) :
    tensorOp (A * B) (S * T) = tensorOp A S * tensorOp B T := by
  ext y a : 2
  simp only [ContinuousLinearMap.mul_apply, tensorOp_apply, Matrix.mul_apply, Finset.sum_smul,
    map_sum, map_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm


end StrongConv.Stable

end
end
end

section
section
open scoped InnerProductSpace
open Matrix Filter Topology

noncomputable section

namespace StrongConv.Stable.Tau

/-! ### Left and right translations on `ℓ²(F_d)` -/

lemma leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    leftReg g f h = f (g⁻¹ * h) := rfl

lemma star_leftReg {d : ℕ} (g : FreeGroup (Fin d)) : star (leftReg g) = leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

/-- The right translation `(R_g f)(h) = f(h g)`. -/
def rightReg {d : ℕ} (g : FreeGroup (Fin d)) : L2Free d →L[ℂ] L2Free d :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun h => f (h * g), by
        have hf := (lp.memℓp f)
        rw [memℓp_gen_iff (by norm_num)] at hf
        show Memℓp (fun h : FreeGroup (Fin d) => f (h * g)) 2
        rw [memℓp_gen_iff (by norm_num)]
        exact (Equiv.mulRight g).summable_iff.mpr hf⟩
      map_add' := fun f f' => by ext h; rfl
      map_smul' := fun c f => by ext h; rfl }
    1
    (by
      intro f
      rw [one_mul]
      apply le_of_eq
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
      congr 1
      exact (Equiv.mulRight g).tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal))

lemma rightReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    rightReg g f h = f (h * g) := rfl

lemma star_rightReg {d : ℕ} (g : FreeGroup (Fin d)) : star (rightReg g) = rightReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [rightReg_apply]
  rw [← (Equiv.mulRight g).tsum_eq]
  simp

lemma commute_leftReg_rightReg {d : ℕ} (a g : FreeGroup (Fin d)) :
    Commute (leftReg a) (rightReg g) := by
  ext f h
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, leftReg_apply, rightReg_apply, mul_assoc]

lemma rightReg_delta_one {d : ℕ} (g : FreeGroup (Fin d)) :
    rightReg g⁻¹ (delta 1) = delta g := by
  classical
  ext h
  simp only [rightReg_apply, delta, lp.single_apply, Pi.single_apply]
  by_cases hh : h = g
  · subst hh; simp
  · rw [if_neg (by intro h'; apply hh; simpa [mul_inv_eq_one] using h'), if_neg hh]

lemma commute_wordOp_rightReg {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) (g : FreeGroup (Fin d)) :
    Commute (wordOp (sLimit d) w) (rightReg g) := by
  unfold wordOp
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
  rcases l with i | i
  · exact commute_leftReg_rightReg _ _
  · simp only [letterOp, sLimit, star_leftReg]
    exact commute_leftReg_rightReg _ _

/-! ### The diagonal right translation on `D` copies -/

variable {D d : ℕ}

abbrev EE (D d : ℕ) := PiLp 2 (fun _ : Fin D => L2Free d)

/-- `1 ⊗ R_g`. -/
def U (D : ℕ) {d : ℕ} (g : FreeGroup (Fin d)) : (EE D d) →L[ℂ] (EE D d) :=
  tensorOp (1 : Matrix (Fin D) (Fin D) ℂ) (rightReg g)

lemma U_single (g : FreeGroup (Fin d)) (a : Fin D) (x : L2Free d) :
    U D g (PiLp.single 2 a x) = PiLp.single 2 a (rightReg g x) := by
  classical
  ext b : 1
  rw [U, tensorOp_apply]
  simp only [Matrix.one_apply, PiLp.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single a]
  · by_cases h : b = a
    · subst h; simp
    · simp [h]
  · intro c _ hc; simp [hc]
  · simp

lemma commute_eval_U (P : NCPoly D d) (g : FreeGroup (Fin d)) :
    Commute (P.eval (sLimit d)) (U D g) := by
  unfold NCPoly.eval
  apply Commute.sum_left
  intro w _
  unfold Commute SemiconjBy
  rw [U, ← tensorOp_mul, ← tensorOp_mul, mul_one, one_mul,
    (commute_wordOp_rightReg w g).eq]

lemma star_U (g : FreeGroup (Fin d)) : star (U D g) = U D g⁻¹ := by
  rw [U, star_tensorOp, star_rightReg, conjTranspose_one, U]

lemma commute_star_eval_U (P : NCPoly D d) (g : FreeGroup (Fin d)) :
    Commute (star (P.eval (sLimit d))) (U D g) := by
  have h := (commute_eval_U P g⁻¹).star_star
  rwa [star_U, inv_inv] at h

/-- A bounded operator vanishing on every `e_a ⊗ δ_g` is zero. -/
lemma eq_zero_of_single_delta (X : (EE D d) →L[ℂ] (EE D d))
    (hX : ∀ a g, X (PiLp.single 2 a (delta g)) = 0) : X = 0 := by
  classical
  have h1 : ∀ a (f : L2Free d), X (PiLp.single 2 a f) = 0 := by
    intro a f
    let L : L2Free d →L[ℂ] EE D d := X.comp
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => L2Free d)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℂ (fun _ : Fin D => L2Free d) a))
    have hL : ∀ x, L x = X (PiLp.single 2 a x) := fun x => rfl
    have hs := lp.hasSum_single (E := fun _ : FreeGroup (Fin d) => ℂ) (p := 2) (by norm_num) f
    have hm := hs.mapL L
    have hz : ∀ g, L (lp.single 2 g (f g)) = 0 := by
      intro g
      have : lp.single 2 g (f g) = (f g) • delta g := by
        rw [delta, ← lp.single_smul]; simp
      rw [this, map_smul, hL, hX, smul_zero]
    simp only [hz] at hm
    rw [← hL]
    exact (hm.unique hasSum_zero)
  ext y : 1
  have : y = ∑ a, PiLp.single 2 a (y a) := by
    ext b; simp [PiLp.single_apply]
  rw [this, map_sum]
  simp [h1]

/-! ### `tr_D ⊗ τ` -/

/-- `e_a ⊗ δ_e`. -/
abbrev vv (D : ℕ) {d : ℕ} (a : Fin D) : EE D d := PiLp.single 2 a (delta 1)

lemma norm_vv (a : Fin D) : ‖(vv D a : EE D d)‖ = 1 := by
  rw [vv, PiLp.norm_single, delta, lp.norm_single (by norm_num)]
  simp

lemma trTau_eq (Y : (EE D d) →L[ℂ] (EE D d)) :
    (trTau Y).re = (D : ℝ)⁻¹ * ∑ a : Fin D, (⟪vv D a, Y (vv D a)⟫_ℂ).re := by
  unfold trTau
  have h1 : ((D : ℂ)⁻¹) = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [h1, Complex.re_ofReal_mul, Complex.re_sum]

lemma re_trTau_le_norm (Y : (EE D d) →L[ℂ] (EE D d)) : (trTau Y).re ≤ ‖Y‖ := by
  rw [trTau_eq]
  have hb : ∀ a : Fin D, (⟪vv D a, Y (vv D a)⟫_ℂ).re ≤ ‖Y‖ := by
    intro a
    calc (⟪vv D a, Y (vv D a)⟫_ℂ).re ≤ ‖⟪vv D a, Y (vv D a)⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖vv D a‖ * ‖Y (vv D a)‖ := norm_inner_le_norm _ _
      _ ≤ ‖vv D a‖ * (‖Y‖ * ‖vv D a‖) := by
          gcongr; exact Y.le_opNorm _
      _ = ‖Y‖ := by rw [norm_vv]; ring
  calc (D : ℝ)⁻¹ * ∑ a : Fin D, (⟪vv D a, Y (vv D a)⟫_ℂ).re
      ≤ (D : ℝ)⁻¹ * ∑ _a : Fin D, ‖Y‖ := by gcongr with a; exact hb a
    _ = ((D : ℝ)⁻¹ * D) * ‖Y‖ := by simp; ring
    _ ≤ ‖Y‖ := by
        rcases Nat.eq_zero_or_pos D with h | h
        · simp [h]
        · rw [inv_mul_cancel₀ (by positivity), one_mul]

lemma re_trTau_nonneg (X : (EE D d) →L[ℂ] (EE D d)) (hX : 0 ≤ X) : 0 ≤ (trTau X).re := by
  have hpos : X.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive X).mp hX
  rw [trTau_eq]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hpos.re_inner_nonneg_right _)

lemma trTau_sub (Y Z : (EE D d) →L[ℂ] (EE D d)) : trTau (Z - Y) = trTau Z - trTau Y := by
  unfold trTau
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib, mul_sub]

lemma trTau_smul (r : ℝ) (Y : (EE D d) →L[ℂ] (EE D d)) : (trTau (r • Y)).re = r * (trTau Y).re := by
  have : r • Y = (r : ℂ) • Y := (Complex.coe_smul r Y).symm
  rw [this]
  unfold trTau
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right, ← Finset.mul_sum]
  rw [mul_left_comm, Complex.re_ofReal_mul]

lemma re_trTau_mono (Y Z : (EE D d) →L[ℂ] (EE D d)) (h : Y ≤ Z) : (trTau Y).re ≤ (trTau Z).re := by
  have := re_trTau_nonneg (Z - Y) (sub_nonneg.mpr h)
  rw [trTau_sub, Complex.sub_re] at this
  linarith

lemma re_trTau_star_mul_self (F : (EE D d) →L[ℂ] (EE D d)) :
    (trTau (star F * F)).re = (D : ℝ)⁻¹ * ∑ a : Fin D, ‖F (vv D a)‖ ^ 2 := by
  rw [trTau_eq]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-! ### The faithfulness argument -/

/-- The cut-off `f(x) = max 0 (min 1 ((x - (M - ε)) / ε))`. -/
def cut (M ε : ℝ) (x : ℝ) : ℝ := max 0 (min 1 ((x - (M - ε)) / ε))

lemma continuous_cut (M ε : ℝ) : Continuous (cut M ε) := by
  unfold cut; fun_prop

lemma cut_nonneg (M ε x : ℝ) : 0 ≤ cut M ε x := le_max_left _ _

lemma cut_le_one (M ε x : ℝ) : cut M ε x ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma cut_eq_zero (M ε x : ℝ) (hε : 0 < ε) (hx : x ≤ M - ε) : cut M ε x = 0 := by
  unfold cut
  apply le_antisymm _ (le_max_left _ _)
  apply max_le le_rfl
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

lemma cut_self (M ε : ℝ) (hε : 0 < ε) : cut M ε M = 1 := by
  unfold cut
  rw [sub_sub_cancel, div_self hε.ne', min_self, max_eq_right zero_le_one]

theorem exists_cut {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (T : A) (hT : 0 ≤ T) (hpos : 0 < ‖T‖) (ε : ℝ) (hε : 0 < ε) (hεM : ε < ‖T‖) :
    ∃ F : A, F ≠ 0 ∧ (∀ b, Commute T b → Commute F b) ∧
      ∀ p : ℕ, (‖T‖ - ε) ^ p • (star F * F) ≤ T ^ p := by
  classical
  set M := ‖T‖ with hM
  have hTsa : IsSelfAdjoint T := hT.isSelfAdjoint
  have : Nontrivial A := nontrivial_of_ne T 0 (norm_pos_iff.mp hpos)
  have hcont := (continuous_cut M ε).continuousOn (s := spectrum ℝ T)
  set F := cfc (cut M ε) T with hF
  have hFsa : IsSelfAdjoint F := cfc_predicate _ _
  have hMspec : M ∈ spectrum ℝ T := CStarAlgebra.norm_mem_spectrum_of_nonneg hT
  have hF0 : F ≠ 0 := by
    intro h0
    have h0' : cfc (cut M ε) T = cfc (fun _ : ℝ => (0 : ℝ)) T := by
      rw [← hF, h0]; exact (cfc_zero ℝ T).symm
    have := eqOn_of_cfc_eq_cfc h0' (hf := hcont) (hg := continuousOn_const) (ha := hTsa) hMspec
    simp only [cut_self M ε hε] at this
    exact one_ne_zero this
  refine ⟨F, hF0, fun b hb => hb.cfc_real _, fun p => ?_⟩
  have hspec : ∀ x ∈ spectrum ℝ T, 0 ≤ x ∧ x ≤ M := by
    intro x hx
    refine ⟨spectrum_nonneg_of_nonneg hT hx, ?_⟩
    exact (Real.le_norm_self x).trans (spectrum.norm_le_norm_of_mem hx)
  have h1 : star F * F = cfc (fun x => cut M ε x * cut M ε x) T := by
    rw [hFsa.star_eq, hF, cfc_mul _ _ T]
  have h2 : T ^ p = cfc (fun x : ℝ => x ^ p) T := (cfc_pow_id T p).symm
  rw [h1, h2, ← cfc_smul .., cfc_le_iff _ _ T]
  intro x hx
  obtain ⟨hx0, hxM⟩ := hspec x hx
  simp only [smul_eq_mul]
  by_cases hxε : x ≤ M - ε
  · rw [cut_eq_zero M ε x hε hxε]; simp; positivity
  · push_neg at hxε
    have hff : cut M ε x * cut M ε x ≤ 1 := by
      nlinarith [cut_nonneg M ε x, cut_le_one M ε x]
    calc (M - ε) ^ p * (cut M ε x * cut M ε x) ≤ (M - ε) ^ p * 1 := by
          gcongr
      _ ≤ x ^ p := by rw [mul_one]; exact pow_le_pow_left₀ (by linarith) hxε.le p

theorem exists_lower (T : (EE D d) →L[ℂ] (EE D d)) (hT : 0 ≤ T)
    (hU : ∀ g : FreeGroup (Fin d), Commute T (U D g)) (hpos : 0 < ‖T‖)
    (ε : ℝ) (hε : 0 < ε) (hεM : ε < ‖T‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, c * (‖T‖ - ε) ^ p ≤ (trTau (T ^ p)).re := by
  classical
  obtain ⟨F, hF0, hFc, hle⟩ := exists_cut T hT hpos ε hε hεM
  have hFU : ∀ g, Commute F (U D g) := fun g => hFc _ (hU g)
  set c := (trTau (star F * F)).re with hc
  have hcpos : 0 < c := by
    rw [hc, re_trTau_star_mul_self]
    by_contra hle'
    push_neg at hle'
    have hsum : ∑ a : Fin D, ‖F (vv D a)‖ ^ 2 ≤ 0 := by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · subst hD; simp
      · have : (0 : ℝ) < (D : ℝ)⁻¹ := by positivity
        by_contra h'
        push_neg at h'
        have := mul_pos this h'
        linarith
    have hzero : ∀ a, F (vv D a) = 0 := by
      intro a
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖F (vv D a)‖)).mp
        (le_antisymm hsum (Finset.sum_nonneg fun a _ => sq_nonneg _)) a (Finset.mem_univ a)
      simpa using h1
    apply hF0
    apply eq_zero_of_single_delta
    intro a g
    have : (PiLp.single 2 a (delta g) : EE D d) = U D g⁻¹ (vv D a) := by
      rw [vv, U_single, rightReg_delta_one]
    rw [this, ← ContinuousLinearMap.mul_apply, (hFU g⁻¹).eq, ContinuousLinearMap.mul_apply,
      hzero, map_zero]
  refine ⟨c, hcpos, fun p => ?_⟩
  have h1 := re_trTau_mono _ _ (hle p)
  have e : (trTau ((‖T‖ - ε) ^ p • (star F * F))).re = (‖T‖ - ε) ^ p * c := trTau_smul _ _
  have h2 : (‖T‖ - ε) ^ p * c ≤ (trTau (T ^ p)).re := e ▸ h1
  linarith [h2]

lemma eval_eq_zero_of_D_eq_zero (P : NCPoly D d) (hD : D = 0) : P.eval (sLimit d) = 0 := by
  subst hD
  ext y a
  exact a.elim0

lemma norm_star_mul_self_gen {A : Type*} [CStarAlgebra A] (x : A) :
    ‖star x * x‖ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self

theorem tendsto_gen (B T : (EE D d) →L[ℂ] (EE D d)) (hTdef : T = star B * B)
    (hTU : ∀ g, Commute T (U D g)) (hD0 : D = 0 → B = 0) :
    Tendsto (fun p : ℕ => (trTau (T ^ p)).re ^ (1 / (2 * (p : ℝ)))) atTop (𝓝 ‖B‖) := by
  have hT : 0 ≤ T := by rw [hTdef]; exact star_mul_self_nonneg B
  have hTn : ‖T‖ = ‖B‖ * ‖B‖ := by rw [hTdef]; exact norm_star_mul_self_gen B
  have hnn : ∀ p : ℕ, 0 ≤ (trTau (T ^ p)).re := fun p =>
    re_trTau_nonneg _ (CStarAlgebra.pow_nonneg hT p)
  -- upper bound
  have hup : ∀ p : ℕ, 1 ≤ p → (trTau (T ^ p)).re ^ (1 / (2 * (p : ℝ))) ≤ ‖B‖ := by
    intro p hp
    have h1 : (trTau (T ^ p)).re ≤ ‖B‖ ^ (2 * p) := by
      calc (trTau (T ^ p)).re ≤ ‖T ^ p‖ := re_trTau_le_norm _
        _ ≤ ‖T‖ ^ p := norm_pow_le' _ (by omega)
        _ = ‖B‖ ^ (2 * p) := by rw [hTn, pow_mul, sq]
    have h2 : (1 / (2 * (p : ℝ))) = ((2 * p : ℕ) : ℝ)⁻¹ := by push_cast; ring
    calc (trTau (T ^ p)).re ^ (1 / (2 * (p : ℝ))) ≤ (‖B‖ ^ (2 * p)) ^ (1 / (2 * (p : ℝ))) :=
          Real.rpow_le_rpow (hnn p) h1 (by positivity)
      _ = ‖B‖ := by rw [h2, Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega)]
  rw [tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact Eventually.of_forall fun p => lt_of_lt_of_le ha0 (Real.rpow_nonneg (hnn p) _)
    push_neg at ha0
    have hBpos : 0 < ‖B‖ := lt_of_le_of_lt ha0 ha
    have hTpos : 0 < ‖T‖ := by rw [hTn]; positivity
    have hD : D ≠ 0 := by
      intro hD
      have := hD0 hD
      rw [this, norm_zero] at hBpos
      exact lt_irrefl _ hBpos
    set M := ‖T‖
    have ha2 : a ^ 2 < M := by rw [hTn]; nlinarith
    set ε := (M - a ^ 2) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hεM : ε < M := by rw [hε]; nlinarith [sq_nonneg a]
    obtain ⟨c, hc, hlow⟩ := exists_lower T hT hTU hTpos ε hε0 hεM
    have hMε : 0 < M - ε := by linarith
    have has : a < Real.sqrt (M - ε) := by
      rw [Real.lt_sqrt ha0]; rw [hε]; linarith
    -- `c ^ (1/(2p)) → 1`
    have hexp : Tendsto (fun p : ℕ => 1 / (2 * (p : ℝ))) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (two_pos : (0:ℝ) < 2)
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp this
    have hcl : Tendsto (fun p : ℕ => c ^ (1 / (2 * (p : ℝ))) * Real.sqrt (M - ε)) atTop
        (𝓝 (Real.sqrt (M - ε))) := by
      have h1 : Tendsto (fun p : ℕ => c ^ (1 / (2 * (p : ℝ)))) atTop (𝓝 (c ^ (0 : ℝ))) :=
        ((Real.continuousAt_const_rpow hc.ne').tendsto).comp hexp
      rw [Real.rpow_zero] at h1
      simpa using h1.mul_const (Real.sqrt (M - ε))
    filter_upwards [hcl.eventually (lt_mem_nhds has), eventually_ge_atTop 1] with p hp hp1
    refine lt_of_lt_of_le hp ?_
    have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    have hpos' : (0 : ℝ) < 2 * p := by linarith
    calc c ^ (1 / (2 * (p : ℝ))) * Real.sqrt (M - ε)
        = (c * (M - ε) ^ p) ^ (1 / (2 * (p : ℝ))) := by
          rw [Real.mul_rpow hc.le (pow_nonneg hMε.le _), Real.sqrt_eq_rpow,
            ← Real.rpow_natCast, ← Real.rpow_mul hMε.le]
          congr 2
          field_simp
      _ ≤ (trTau (T ^ p)).re ^ (1 / (2 * (p : ℝ))) :=
          Real.rpow_le_rpow (by positivity) (hlow p) (by positivity)
  · intro b hb
    filter_upwards [eventually_ge_atTop 1] with p hp
    exact lt_of_le_of_lt (hup p hp) hb

theorem tendsto_re_trTau_pow_rpow_dev (P : NCPoly D d) :
    Tendsto (fun p : ℕ => (trTau ((star (P.eval (sLimit d)) * P.eval (sLimit d)) ^ p)).re ^
        (1 / (2 * (p : ℝ)))) atTop (𝓝 ‖P.eval (sLimit d)‖) :=
  tendsto_gen _ _ rfl (fun g => (commute_star_eval_U P g).mul_left (commute_eval_U P g))
    (eval_eq_zero_of_D_eq_zero P)

end StrongConv.Stable.Tau

end
end
end

section
open StrongConv

open Polynomial Filter Topology


theorem solution {D d : ℕ} (P : NCPoly D d) :
    Tendsto (fun p : ℕ => (trTau ((star (P.eval (sLimit d)) * P.eval (sLimit d)) ^ p)).re ^
        (1 / (2 * (p : ℝ)))) atTop (𝓝 ‖P.eval (sLimit d)‖) := by
  apply StrongConv.Stable.Tau.tendsto_re_trTau_pow_rpow_dev <;> assumption

end
