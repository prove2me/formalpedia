-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.KRep.kUnit_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:15.351262+00:00
-- url     : https://prove2.me/submissions/c94e0783-f45b-4edb-8f0e-76c2c72477d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_RelOpCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
private theorem KRep.rel_op_curve {ε : Fin n → Bool} (R : KRep ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    R.op (γ t) = NormedSpace.exp ((t : ℂ) • R.dτ X) := by
  have hmul : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun a b => rfl
  have hinj : ∀ a b : KG ε, toMK a = toMK b → a = b := fun a b h =>
    Subtype.ext (Subtype.ext (Units.ext h))
  have hexp : ∀ s u : ℝ, NormedSpace.exp (((s + u : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X) := by
    intro s u
    rw [Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have hγadd : ∀ s u : ℝ, γ (s + u) = γ s * γ u := fun s u =>
    hinj _ _ (by rw [hmul, hγ, hγ, hγ, hexp])
  have hγ0 : γ 0 = 1 := hinj _ _ (by rw [hγ, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]; rfl)
  have hop_mul : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b := by
    intro a b; simp [KRep.op, map_mul]
  have hop_one : R.op 1 = 1 := by simp [KRep.op]
  set A := R.dτ X with hA
  have hd0 : HasDerivAt (fun s => R.op (γ s)) A 0 := R.hasDeriv X hX γ hγ
  have hd : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u)) (R.op (γ s) * A) s := by
    intro s
    have h1 : HasDerivAt (fun u => R.op (γ s) * R.op (γ u)) (R.op (γ s) * A) (s - s) := by
      rw [sub_self]; exact hd0.const_mul _
    refine (h1.comp_sub_const s s).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    show R.op (γ x) = R.op (γ s) * R.op (γ (x - s))
    rw [← hop_mul, ← hγadd]
    congr 2
    ring
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • (-A)))
      (NormedSpace.exp ((s : ℂ) • (-A)) * (-A)) s := by
    intro s
    first
      | exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) (-A) (s : ℂ)).comp_ofReal
      | exact HasDerivAt.comp_ofReal (e := fun u : ℂ => NormedSpace.exp (u • (-A)))
          (hasDerivAt_exp_smul_const (-A) (s : ℂ))
      | (simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s)
      | (simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s)
  have hcomm : ∀ s : ℝ, A * NormedSpace.exp ((s : ℂ) • (-A)) = NormedSpace.exp ((s : ℂ) • (-A)) * A :=
    fun s => (((Commute.refl A).neg_right.smul_right (s : ℂ)).exp_right).eq
  have hg : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u) * NormedSpace.exp ((u : ℂ) • (-A))) 0 s := by
    intro s
    have h := (hd s).mul (hE s)
    refine h.congr_deriv ?_
    rw [mul_assoc, hcomm, mul_neg, mul_neg, add_neg_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv)
  have hg0 : R.op (γ 0) * NormedSpace.exp (((0 : ℝ) : ℂ) • (-A)) = 1 := by
    rw [hγ0, hop_one, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul]
  have hEE : NormedSpace.exp ((t : ℂ) • (-A)) * NormedSpace.exp ((t : ℂ) • A) = 1 := by
    letI : NormedAlgebra ℚ (R.V →L[ℂ] R.V) := by
      first
        | exact NormedAlgebra.restrictScalars ℚ ℂ _
        | exact NormedAlgebra.restrictScalars ℚ ℝ _
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl A).neg_left.smul_left _ |>.smul_right _),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]
  calc R.op (γ t) = R.op (γ t) * (NormedSpace.exp ((t : ℂ) • (-A)) * NormedSpace.exp ((t : ℂ) • A)) := by
        rw [hEE, mul_one]
    _ = (R.op (γ t) * NormedSpace.exp ((t : ℂ) • (-A))) * NormedSpace.exp ((t : ℂ) • A) := by
        rw [mul_assoc]
    _ = NormedSpace.exp ((t : ℂ) • A) := by
        rw [hconst t 0, hg0, one_mul]
private theorem exists_curve_toMK_eq_exp_smul_of_inK {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    ∃ γ : ℝ → KG ε, ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X) := by
  obtain ⟨hG, hJ⟩ := hX
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hskew : Xᴴ = -X := by
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by rw [hJ]; exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -X := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hE : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • (-X)) := by
    intro t
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hskew, Complex.star_def, Complex.conj_ofReal]
  have hinv1 : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (-X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
    intro t
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_left.smul_left _).smul_right _),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]
  have hinv2 : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X)) = 1 := by
    intro t
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_right.smul_left _).smul_right _),
      smul_neg, add_neg_cancel, NormedSpace.exp_zero]
  have hcJ : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • X) := by
    intro t
    have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJJ
    have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
    have hXc : Jm ε * ((t : ℂ) • X) * (Jm ε)⁻¹ = (t : ℂ) • X := by
      rw [hJi, Matrix.mul_smul, Matrix.smul_mul, ← hJ, Matrix.mul_assoc, hJJ, Matrix.mul_one]
    have h := Matrix.exp_conj (Jm ε) ((t : ℂ) • X) hJu
    rw [hXc, hJi] at h
    calc NormedSpace.exp ((t : ℂ) • X) * Jm ε
        = Jm ε * NormedSpace.exp ((t : ℂ) • X) * Jm ε * Jm ε := by rw [← h]
      _ = Jm ε * NormedSpace.exp ((t : ℂ) • X) := by rw [Matrix.mul_assoc _ (Jm ε), hJJ, Matrix.mul_one]
  let u : ℝ → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun t =>
    ⟨NormedSpace.exp ((t : ℂ) • X), NormedSpace.exp ((t : ℂ) • (-X)), hinv2 t, hinv1 t⟩
  have hU : ∀ t : ℝ, u t ∈ UJ ε := by
    intro t
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
    rw [Matrix.mul_assoc, ← hcJ, ← Matrix.mul_assoc, hE, hinv1, Matrix.one_mul]
  have hK : ∀ t : ℝ, (⟨u t, hU t⟩ : UJ ε) ∈ KG ε := by
    intro t
    refine ⟨?_, hcJ t⟩
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    show NormedSpace.exp ((t : ℂ) • X) * (NormedSpace.exp ((t : ℂ) • X))ᴴ = 1
    rw [hE, hinv2]
  exact ⟨fun t => ⟨⟨u t, hU t⟩, hK t⟩, fun t => rfl⟩
private theorem KRep.rel_star_dτ {ε : Fin n → Bool} (R : KRep ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : star (R.dτ X) = -R.dτ X := by
  obtain ⟨γ, hγ⟩ := exists_curve_toMK_eq_exp_smul_of_inK hX
  set A := R.dτ X with hA
  have hf : ∀ s : ℝ, R.op (γ s) = NormedSpace.exp ((s : ℂ) • A) := R.rel_op_curve hX γ hγ
  have hEE : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • (-A)) * NormedSpace.exp ((s : ℂ) • A) = 1 := by
    intro s
    letI : NormedAlgebra ℚ (R.V →L[ℂ] R.V) := by
      first
        | exact NormedAlgebra.restrictScalars ℚ ℂ _
        | exact NormedAlgebra.restrictScalars ℚ ℝ _
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl A).neg_left.smul_left _ |>.smul_right _),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]
  have hU : ∀ s : ℝ, R.op (γ s) * star (R.op (γ s)) = 1 := fun s => (R.τ (γ s)).2.2
  have hstar : ∀ s : ℝ, star (NormedSpace.exp ((s : ℂ) • A)) = NormedSpace.exp ((s : ℂ) • (-A)) := by
    intro s
    calc star (NormedSpace.exp ((s : ℂ) • A))
        = (NormedSpace.exp ((s : ℂ) • (-A)) * NormedSpace.exp ((s : ℂ) • A)) *
            star (NormedSpace.exp ((s : ℂ) • A)) := by rw [hEE, one_mul]
      _ = NormedSpace.exp ((s : ℂ) • (-A)) := by rw [mul_assoc, ← hf, hU, mul_one]
  have hfun : (fun s : ℝ => NormedSpace.exp ((s : ℂ) • star A)) =
      fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-A)) := by
    funext s
    rw [← hstar]
    first
      | rw [NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal]
      | rw [← NormedSpace.exp_star, star_smul, Complex.star_def, Complex.conj_ofReal]
      | rw [star_exp, star_smul, Complex.star_def, Complex.conj_ofReal]
  have d1 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • star A))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • star A) * star A) 0 := by
    first
      | exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) (star A) ((0 : ℝ) : ℂ)).comp_ofReal
      | (simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (star A) (0 : ℝ))
      | (simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (star A) (0 : ℝ))
  have d2 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-A)))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • (-A)) * (-A)) 0 := by
    first
      | exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) (-A) ((0 : ℝ) : ℂ)).comp_ofReal
      | (simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ))
      | (simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ))
  rw [hfun] at d1
  have h := d1.unique d2
  simpa using h
section MatDeriv
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end MatDeriv
private theorem inK_of_support_sign_eq_of_skewAdjoint {ε : Fin n → Bool} (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ i j, X i j ≠ 0 → ε i = ε j) (hs : Xᴴ = -X) : inK ε X := by
  have hc : X * Jm ε = Jm ε * X := by
    ext i j
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : X i j = 0
    · simp [h]
    · rw [hX i j h, mul_comm]
  refine ⟨?_, hc⟩
  unfold inG
  rw [hs, neg_mul, hc, neg_add_cancel]
private theorem inK_single_sub_single_and_I_smul_add_of_sign_eq {ε : Fin n → Bool} {a b : Fin n} (hab : ε a = ε b) :
    inK ε (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) ∧
      inK ε (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
  constructor
  · apply inK_of_support_sign_eq_of_skewAdjoint
    · intro i j h
      simp only [Matrix.sub_apply, Matrix.single_apply] at h
      by_cases e1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := e1; exact hab
      · by_cases e2 : b = i ∧ a = j
        · obtain ⟨rfl, rfl⟩ := e2; exact hab.symm
        · simp [e1, e2] at h
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply,
        show (a = j ∧ b = i) ↔ (b = i ∧ a = j) from and_comm, show (b = j ∧ a = i) ↔ (a = i ∧ b = j) from and_comm]
      by_cases e1 : a = i ∧ b = j <;> by_cases e2 : b = i ∧ a = j <;> simp [e1, e2]
  · apply inK_of_support_sign_eq_of_skewAdjoint
    · intro i j h
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply] at h
      by_cases e1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := e1; exact hab
      · by_cases e2 : b = i ∧ a = j
        · obtain ⟨rfl, rfl⟩ := e2; exact hab.symm
        · simp [e1, e2] at h
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply,
        Matrix.single_apply, smul_eq_mul,
        show (a = j ∧ b = i) ↔ (b = i ∧ a = j) from and_comm, show (b = j ∧ a = i) ↔ (a = i ∧ b = j) from and_comm]
      by_cases e1 : a = i ∧ b = j <;> by_cases e2 : b = i ∧ a = j <;>
        simp [e1, e2, Complex.conj_I, map_ofNat] <;> ring
private theorem KRep.rel_star_dτ_single {ε : Fin n → Bool} (R : KRep ε)
    {a b : Fin n} (hab : ε a = ε b) :
    star (R.dτ (Matrix.single a b 1)) = R.dτ (Matrix.single b a 1) := by
  have h1 := (inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hab).1
  have h2 := (inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hab).2
  have s1 := R.rel_star_dτ h1
  have s2 := R.rel_star_dτ h2
  simp only [map_sub, map_add, map_smul, star_sub, star_add, star_smul, Complex.star_def, Complex.conj_I] at s1 s2
  set A := R.dτ (Matrix.single a b 1)
  set B := R.dτ (Matrix.single b a 1)
  have h3 : star A - star B = B - A := by rw [s1]; abel
  have h4 : star A + star B = A + B := by
    have := congrArg (fun x => Complex.I • x) s2
    exact (by simpa [smul_add, smul_smul, Complex.I_mul_I, neg_smul, smul_neg, mul_neg] using this :
      star A + star B = B + A).trans (add_comm B A)
  have h5 : (2 : ℂ) • star A = (2 : ℂ) • B := by
    rw [two_smul, two_smul]
    calc star A + star A = (star A - star B) + (star A + star B) := by abel
      _ = (B - A) + (A + B) := by rw [h3, h4]
      _ = B + B := by abel
  exact smul_right_injective _ two_ne_zero h5
end ReciprocityTheory.ChartRestriction.DS.HW
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
namespace KRep
theorem _root_.solution {ε : Fin n → Bool} (R : KRep ε) : Formalism.REAL.KUnit ε R.units := by
  intro a b hab x y
  have h := R.rel_star_dτ_single hab
  simp only [KRep.units, ContinuousLinearMap.coe_coe]
  rw [← h, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
end KRep
end ReciprocityTheory.ChartRestriction.DS.HW
