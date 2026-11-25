-- Prove2me | solution 1 for PI.WMI.modelIso_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:20.354744+00:00
-- url     : https://prove2.me/submissions/44c0d01d-4953-48e0-8576-a10d23b10ba1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_Assembly
import Theorems.Thm_PI_WMI_det_ne_zero_of_mem_K
import Theorems.Thm_PI_WMI_detPoly_ne_zero
import Theorems.Thm_PI_WMI_rowAct_detPoly
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylNonDom
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution (hA : PolyExt) (hI : LamInt) (hT : TorusEig) (hL : LowerInv)
    (hM : ModelMap) (hD : DetSplit) (hH : PI.HwIrred) : PI.ModelIso := by
  intro N Λ H _ _ σ S hU hK
  obtain ⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩ := hK
  have hK' : IsKTypeOf (allPos N) σ Λ S := ⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩
  haveI := hfin
  obtain ⟨K, P, hP, hPσ⟩ := hA N H σ S hU hfin hstab
  choose μ hμ using hI N Λ H σ v0 hU hv0ne hv0w
  let w0 : S := ⟨v0, hv0S⟩
  have hw0ne : w0 ≠ 0 := by
    intro h; apply hv0ne
    have := congrArg Subtype.val h
    simpa [w0] using this
  have hT' := hT N Λ H σ S K P hU hstab hPσ w0 hv0w
  have hL' := hL N Λ H σ S K P hU hK' hP hPσ w0 hv0w
  have hT'' : ∀ (θ : Fin N → ℝ) (x : S), ⟪w0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪w0, x⟫_ℂ := by
    intro θ x; rw [hT' θ x]; simp only [hμ]
  obtain ⟨ν, F, hν, hFmem, hF0, hFint⟩ := hM N S P w0 μ K hP hw0ne hT'' hL'
  have hanti : Antitone ν := by
    intro l j hlj
    by_contra hlt
    push_neg at hlt
    rcases eq_or_lt_of_le hlj with h | h
    · subst h; exact lt_irrefl _ hlt
    · have hbot := dualWeylNonDom ℂ N N ν ⟨l, j, h, hlt⟩
      have := hFmem w0
      rw [hbot, Submodule.mem_bot] at this
      exact hF0 this
  have hμanti : Antitone μ := by
    intro a b hab
    have h1 := hν a
    have h2 := hν b
    have h3 : (ν b : ℤ) ≤ ν a := by exact_mod_cast hanti hab
    omega
  let lam : DomWeight N := ⟨μ, hμanti⟩
  refine ⟨lam, fun a => hμ a, ?_⟩
  let c : ℕ := if h : 0 < N then ν ⟨N - 1, by omega⟩ else 0
  have hnat : ∀ a, lam.natW a + c = ν a := by
    intro a
    have hN : 0 < N := a.pos
    have h1 := hν a
    have h2 := hν ⟨N - 1, by omega⟩
    have h3 : ν ⟨N - 1, by omega⟩ ≤ ν a := hanti (by rw [Fin.le_def]; simp; omega)
    have h3' : (ν ⟨N - 1, by omega⟩ : ℤ) ≤ ν a := by exact_mod_cast h3
    simp only [DomWeight.natW, DomWeight.detShift, c, dif_pos hN, lam]
    omega
  have hlast : ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 := by
    intro h; simp [DomWeight.natW, DomWeight.detShift, h, lam]
  have hsplit := hD N lam.natW c hlast
  have hνeq : (fun a => lam.natW a + c) = ν := funext hnat
  have hFmem' : ∀ x, F x ∈ dualWeyl ℂ N N (fun a => lam.natW a + c) := by
    intro x; rw [hνeq]; exact hFmem x
  let mulD : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ :=
    LinearMap.mulLeft ℂ (detPoly N ^ c)
  have hmulD_inj : Function.Injective mulD := by
    intro f g hfg
    simp only [mulD, LinearMap.mulLeft_apply] at hfg
    exact mul_left_cancel₀ (pow_ne_zero _ (detPoly_ne_zero N)) hfg
  let U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
    nablaSq ℂ N lam ⊓ (LinearMap.range F).comap mulD
  have hUst : ∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U := by
    intro g f hf
    obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.mp hf
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hf2)
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · unfold sqAct
      exact Submodule.smul_mem _ _ (dualWeylRowStable ℂ N N _ _ f hf1)
    · set dg := (g : Matrix (Fin N) (Fin N) ℂ).det with hdgdef
      have hdg : dg ≠ 0 := by
        have := (Matrix.GeneralLinearGroup.det g).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
      refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr
        ⟨(detPow ℂ N g lam.detShift * (dg ^ c)⁻¹) • P (g : Matrix (Fin N) (Fin N) ℂ) x, ?_⟩)
      rw [map_smul, hFint, hx]
      simp only [mulD, LinearMap.mulLeft_apply, sqAct]
      rw [map_mul, map_pow, rowAct_detPoly, Matrix.det_transpose]
      have key : C ((dg ^ c)⁻¹) * C dg ^ c = (1 : MvPolynomial (Fin N × Fin N) ℂ) := by
        rw [← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hdg), C_1]
      simp only [smul_eq_C_mul, C_mul]
      linear_combination (C (detPow ℂ N g lam.detShift) * detPoly N ^ c *
        rowAct ℂ (n := N) (g : Matrix (Fin N) (Fin N) ℂ)ᵀ f) * key
  obtain ⟨f0, hf0mem, hf0eq⟩ := hsplit (F w0) (hFmem' w0)
  have hf0U : f0 ∈ U := Submodule.mem_inf.mpr ⟨hf0mem, Submodule.mem_comap.mpr
    (LinearMap.mem_range.mpr ⟨w0, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf0eq⟩)⟩
  have hf0ne : f0 ≠ 0 := by
    intro h; apply hF0; rw [hf0eq, h, mul_zero]
  have hUeq : U = nablaSq ℂ N lam := by
    rcases (hH N lam).2.1 U inf_le_left hUst with h | h
    · exfalso; rw [h, Submodule.mem_bot] at hf0U; exact hf0ne hf0U
    · exact h
  have hFinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ H := (LinearMap.ker F).map S.subtype
    have hS'le : S' ≤ S := by
      rintro _ ⟨y, _, rfl⟩; exact y.2
    have hS'st : IsKStableOn (allPos N) σ S' := by
      rintro g hg _ ⟨y, hy, rfl⟩
      have hd : g.det ^ K ≠ 0 := pow_ne_zero _ (det_ne_zero_of_mem_K hg)
      refine ⟨(g.det ^ K)⁻¹ • P g y, ?_, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker] at hy ⊢
        rw [map_smul, hFint, hy, map_zero, smul_zero]
      · simp only [Submodule.subtype_apply, Submodule.coe_smul, hPσ g hg y, smul_smul,
          inv_mul_cancel₀ hd, one_smul]
    rcases hirr S' hS'le hS'st with h | h
    · rw [eq_bot_iff]
      intro y hy
      have hyS : (y : H) ∈ S' := ⟨y, hy, rfl⟩
      rw [h, Submodule.mem_bot] at hyS
      rw [Submodule.mem_bot]
      exact Subtype.ext hyS
    · exfalso
      have hv : v0 ∈ S' := by rw [h]; exact hv0S
      obtain ⟨y, hy, hyv⟩ := hv
      have hyw : y = w0 := Subtype.ext hyv
      rw [hyw] at hy
      exact hF0 hy
  let φ : U →ₗ[ℂ] LinearMap.range F :=
    LinearMap.codRestrict (LinearMap.range F) (mulD ∘ₗ U.subtype)
      (fun u => Submodule.mem_comap.mp (Submodule.mem_inf.mp u.2).2)
  have hφ : Function.Bijective φ := by
    constructor
    · intro u v huv
      have := congrArg Subtype.val huv
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
      exact Subtype.ext (hmulD_inj this)
    · rintro ⟨z, x, rfl⟩
      obtain ⟨f', hf'mem, hf'eq⟩ := hsplit (F x) (hFmem' x)
      refine ⟨⟨f', Submodule.mem_inf.mpr ⟨hf'mem, Submodule.mem_comap.mpr
        (LinearMap.mem_range.mpr ⟨x, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf'eq⟩)⟩⟩, ?_⟩
      apply Subtype.ext
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, mulD,
        LinearMap.mulLeft_apply]
      exact hf'eq.symm
  calc Module.finrank ℂ S = Module.finrank ℂ (LinearMap.range F) :=
        (LinearMap.finrank_range_of_inj hFinj).symm
    _ = Module.finrank ℂ U := (LinearEquiv.ofBijective φ hφ).finrank_eq.symm
    _ = Module.finrank ℂ (nablaSq ℂ N lam) := (LinearEquiv.ofEq _ _ hUeq).finrank_eq
end PI.WMI
