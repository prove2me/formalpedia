-- Prove2me | solution 1 for PeriodPair.discriminant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6cfc278d-1a2e-5208-a95f-f24a2956696e

import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_discriminant_ne_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

section
section

noncomputable section

open scoped MatrixGroups UpperHalfPlane
p2m_open "UpperHalfPlane ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm ModularFormClass EisensteinSeries PowerSeries"

namespace ModularForm
p2m_export "ModularForm" "sub_apply toCuspForm E coe_mul discriminant tendsto_atImInfty_tprod_one_sub_eta_q_pow discriminant_eq_q_prod E₄_qExpansion_coeff_one ext smul_apply E₄ mcast E₆ discriminant_ne_zero E₆_qExpansion_coeff_one mul"
p2m_open "ModularForm"

def kw_E4cube : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by ring) ((E₄.mul E₄).mul E₄)

def kw_E6sq : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by ring) (E₆.mul E₆)

@[scoped simp] theorem kw_E4cube_apply (τ : ℍ) : kw_E4cube τ = E₄ τ ^ 3 := by
  show ((E₄.mul E₄).mul E₄) τ = E₄ τ ^ 3
  simp only [ModularForm.coe_mul, Pi.mul_apply]; ring

@[scoped simp] theorem kw_E6sq_apply (τ : ℍ) : kw_E6sq τ = E₆ τ ^ 2 := by
  show (E₆.mul E₆) τ = E₆ τ ^ 2
  simp only [ModularForm.coe_mul, Pi.mul_apply]; ring

def kw_E4cube_sub_E6sq : ModularForm 𝒮ℒ 12 := kw_E4cube - kw_E6sq

@[scoped simp] theorem kw_E4cube_sub_E6sq_apply (τ : ℍ) :
    kw_E4cube_sub_E6sq τ = E₄ τ ^ 3 - E₆ τ ^ 2 := by
  simp [kw_E4cube_sub_E6sq, ModularForm.sub_apply]

private theorem kw_qExpansion_E4cube :
    qExpansion 1 (kw_E4cube : ℍ → ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) ^ 3 := by
  show qExpansion 1 (((E₄.mul E₄).mul E₄ : ModularForm _ _) : ℍ → ℂ) = _
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]
  ring

private theorem kw_qExpansion_E6sq :
    qExpansion 1 (kw_E6sq : ℍ → ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) ^ 2 := by
  show qExpansion 1 ((E₆.mul E₆ : ModularForm _ _) : ℍ → ℂ) = _
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]
  ring

private theorem kw_qExpansion_E4cube_sub_E6sq :
    qExpansion 1 (kw_E4cube_sub_E6sq : ℍ → ℂ)
      = qExpansion 1 (E₄ : ℍ → ℂ) ^ 3 - qExpansion 1 (E₆ : ℍ → ℂ) ^ 2 := by
  rw [show (kw_E4cube_sub_E6sq : ℍ → ℂ) = (kw_E4cube : ℍ → ℂ) - (kw_E6sq : ℍ → ℂ) from
      rfl,
    ModularFormClass.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    kw_qExpansion_E4cube, kw_qExpansion_E6sq]

private theorem kw_E4_coeff_zero : (qExpansion 1 (E₄ : ℍ → ℂ)).coeff 0 = 1 :=
  E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩

private theorem kw_E6_coeff_zero : (qExpansion 1 (E₆ : ℍ → ℂ)).coeff 0 = 1 :=
  E_qExpansion_coeff_zero (by norm_num) ⟨3, rfl⟩

theorem kw_E4cube_sub_E6sq_coeff_zero :
    (qExpansion 1 (kw_E4cube_sub_E6sq : ℍ → ℂ)).coeff 0 = 0 := by
  rw [kw_qExpansion_E4cube_sub_E6sq, PowerSeries.coeff_zero_eq_constantCoeff, map_sub, map_pow,
    map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, kw_E4_coeff_zero, kw_E6_coeff_zero]
  ring

private theorem kw_antidiagonal_one :
    (Finset.HasAntidiagonal.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} := by decide

private theorem kw_coeff_one_mul (p q : PowerSeries ℂ) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [PowerSeries.coeff_mul, kw_antidiagonal_one]
  simp

private theorem kw_coeff_one_sq (p : PowerSeries ℂ) :
    (p ^ 2).coeff 1 = 2 * p.coeff 0 * p.coeff 1 := by
  rw [sq, kw_coeff_one_mul]; ring

private theorem kw_coeff_one_cube (p : PowerSeries ℂ) :
    (p ^ 3).coeff 1 = 3 * p.coeff 0 ^ 2 * p.coeff 1 := by
  have hsq0 : (p ^ 2).coeff 0 = p.coeff 0 ^ 2 := by
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
  rw [show p ^ 3 = p * p ^ 2 from by ring, kw_coeff_one_mul, kw_coeff_one_sq, hsq0]
  ring

theorem kw_E4cube_sub_E6sq_coeff_one :
    (qExpansion 1 (kw_E4cube_sub_E6sq : ℍ → ℂ)).coeff 1 = 1728 := by
  rw [kw_qExpansion_E4cube_sub_E6sq, map_sub, kw_coeff_one_cube, kw_coeff_one_sq,
    kw_E4_coeff_zero, kw_E6_coeff_zero, E₄_qExpansion_coeff_one, E₆_qExpansion_coeff_one]
  ring

def kw_E4cube_sub_E6sq_cuspForm : CuspForm 𝒮ℒ 12 :=
  toCuspForm kw_E4cube_sub_E6sq kw_E4cube_sub_E6sq_coeff_zero

@[scoped simp] theorem kw_E4cube_sub_E6sq_cuspForm_apply (τ : ℍ) :
    kw_E4cube_sub_E6sq_cuspForm τ = E₄ τ ^ 3 - E₆ τ ^ 2 :=
  kw_E4cube_sub_E6sq_apply τ

theorem kw_exists_smul_discriminant_eq_E4cube_sub_E6sq :
    ∃ c : ℂ, c ≠ 0 ∧ (∀ τ : ℍ, E₄ τ ^ 3 - E₆ τ ^ 2 = c * discriminant τ) ∧
      c * (qExpansion 1 (discriminant : ℍ → ℂ)).coeff 1 = 1728 := by

  obtain ⟨c, hc⟩ :=
    CuspForm.exists_smul_discriminant_of_weight_eq_twelve kw_E4cube_sub_E6sq_cuspForm

  have hpt : ∀ τ : ℍ, E₄ τ ^ 3 - E₆ τ ^ 2 = c * discriminant τ := fun τ => by
    have h := DFunLike.congr_fun hc τ
    simp only [CuspForm.smul_apply, CuspForm.coe_discriminant, smul_eq_mul,
      kw_E4cube_sub_E6sq_cuspForm_apply] at h
    exact h.symm

  have hcoeff : c * (qExpansion 1 (discriminant : ℍ → ℂ)).coeff 1 = 1728 := by
    have hfun : (kw_E4cube_sub_E6sq_cuspForm : ℍ → ℂ)
        = c • (CuspForm.discriminant : ℍ → ℂ) := by
      exact_mod_cast congrArg DFunLike.coe hc.symm
    have := kw_E4cube_sub_E6sq_coeff_one
    rw [show (kw_E4cube_sub_E6sq : ℍ → ℂ) = (kw_E4cube_sub_E6sq_cuspForm : ℍ → ℂ) from rfl,
      hfun, ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_smul, smul_eq_mul, CuspForm.coe_discriminant] at this
    exact this

  refine ⟨c, ?_, hpt, hcoeff⟩
  intro hzero
  rw [hzero, zero_mul] at hcoeff
  exact absurd hcoeff (by norm_num)

theorem kw_E4cube_ne_E6sq (τ : ℍ) : E₄ τ ^ 3 ≠ E₆ τ ^ 2 := by
  obtain ⟨c, hc, hpt, -⟩ := kw_exists_smul_discriminant_eq_E4cube_sub_E6sq
  intro h
  have := hpt τ
  rw [h, sub_self] at this
  exact mul_ne_zero hc (discriminant_ne_zero τ) this.symm

end ModularForm
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"
end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section
section

noncomputable section

open UpperHalfPlane Complex

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ latticeEquivProd g₃ derivWeierstrassP_sq ω₂ indep latticeEquiv_symm_apply G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_zero IsUniformization jLattice JSurjective ofTau ofTau_lattice scale_indep scale scale_ω₁ scale_ω₂ sublatticeIndex"
p2m_open "PeriodPair"

theorem kw_ofTau_latticeEquivProd_symm_apply (τ : ℍ) (p : ℤ × ℤ) :
    ((ofTau τ).latticeEquivProd.symm p : ℂ) = p.1 * (τ : ℂ) + p.2 := by
  rw [latticeEquiv_symm_apply]; simp

end PeriodPair
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"
end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section
section

open Complex Filter Set

p2m_open_scoped "PeriodPair P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ latticeEquivProd g₃ derivWeierstrassP_sq ω₂ indep latticeEquiv_symm_apply G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_zero IsUniformization jLattice JSurjective ofTau ofTau_lattice scale_indep scale scale_ω₁ scale_ω₂ sublatticeIndex"
p2m_open "PeriodPair"

variable (L : PeriodPair)

section Liouville

end Liouville
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section Curve

end Curve
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section HalfPeriods

end HalfPeriods
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section ToPoint

end ToPoint
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section JInvariant

end JInvariant
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section Isogeny

end Isogeny
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

end PeriodPair
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

namespace Projectivization
p2m_export "Projectivization" "map card"
p2m_open "Projectivization"

open scoped LinearAlgebra.Projectivization

end Projectivization
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"
end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section
section

noncomputable section

open scoped UpperHalfPlane Real
p2m_open "Complex UpperHalfPlane EisensteinSeries ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ latticeEquivProd g₃ derivWeierstrassP_sq ω₂ indep latticeEquiv_symm_apply G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_zero IsUniformization jLattice JSurjective ofTau ofTau_lattice scale_indep scale scale_ω₁ scale_ω₂ sublatticeIndex"
p2m_open "PeriodPair"

theorem kw_G_ofTau_eq {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    (ofTau τ).G k = 2 * riemannZeta k * E hk τ := by

  rw [G, ← (ofTau τ).latticeEquivProd.symm.toEquiv.tsum_eq]

  simp only [LinearEquiv.coe_toEquiv, kw_ofTau_latticeEquivProd_symm_apply]

  have hstep : ∀ p : ℤ × ℤ,
      ((↑p.1 * (τ : ℂ) + ↑p.2) ^ k)⁻¹ = eisSummand k ((finTwoArrowEquiv ℤ).symm p) τ := by
    intro p
    simp only [eisSummand, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, _root_.zpow_neg, zpow_natCast]
  simp only [hstep]
  rw [(finTwoArrowEquiv ℤ).symm.tsum_eq (f := fun v => eisSummand (k : ℤ) v τ),
    tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ]

  have hE : (E hk : ℍ → ℂ) τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [hE]; ring

end PeriodPair
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

namespace ModularCurve

theorem kw_riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by

  have hb5 : bernoulli' 5 = 0 := by
    have : Nat.choose 5 2 = 10 := by decide
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, this]
  have hb6 : bernoulli' 6 = 1 / 42 := by
    have h62 : Nat.choose 6 2 = 15 := by decide
    have h64 : Nat.choose 6 4 = 15 := by decide
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, hb5, h62, h64]
  have hb : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), hb6]

  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  simp only [show 2 * 3 = 6 from rfl, Nat.reduceMul, Nat.cast_ofNat, hb,
    show (6 : ℕ).factorial = 720 from by decide] at h
  rw [show (2 * (3 : ℂ) : ℂ) = (6 : ℂ) by ring] at h
  push_cast at h
  rw [h]; ring

end ModularCurve
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ latticeEquivProd g₃ derivWeierstrassP_sq ω₂ indep latticeEquiv_symm_apply G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_zero IsUniformization jLattice JSurjective ofTau ofTau_lattice scale_indep scale scale_ω₁ scale_ω₂ sublatticeIndex"
p2m_open "PeriodPair"

open ModularCurve

theorem kw_g₂_ofTau (τ : ℍ) :
    (ofTau τ).g₂ = (4 * (π : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [g₂, kw_G_ofTau_eq (by norm_num : (3:ℕ) ≤ 4) τ,
    show ((4 : ℕ) : ℂ) = (4 : ℂ) by push_cast; ring, riemannZeta_four]
  ring

theorem kw_g₃_ofTau (τ : ℍ) :
    (ofTau τ).g₃ = (8 * (π : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [g₃, kw_G_ofTau_eq (by norm_num : (3:ℕ) ≤ 6) τ,
    show ((6 : ℕ) : ℂ) = (6 : ℂ) by push_cast; ring, kw_riemannZeta_six]
  ring

end PeriodPair
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"
end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section
section

noncomputable section

p2m_open_scoped "PeriodPair P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ latticeEquivProd g₃ derivWeierstrassP_sq ω₂ indep latticeEquiv_symm_apply G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_zero IsUniformization jLattice JSurjective ofTau ofTau_lattice scale_indep scale scale_ω₁ scale_ω₂ sublatticeIndex"
p2m_open "PeriodPair"

variable (L : PeriodPair)

section Scale

variable (α : ℂˣ)

private def mulLeftR (a : ℂ) : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ a

@[scoped simp] private theorem mulLeftR_apply (a z : ℂ) : mulLeftR a z = a * z := rfl

private theorem mulLeftR_injective {a : ℂ} (ha : a ≠ 0) :
    Function.Injective (mulLeftR a) := fun _ _ h => by
  simpa using mul_left_cancel₀ ha h

private def mulLeftZ (a : ℂ) : ℂ →ₗ[ℤ] ℂ := (mulLeftR a).restrictScalars ℤ

@[scoped simp] private theorem mulLeftZ_apply (a z : ℂ) : mulLeftZ a z = a * z := rfl

private theorem _root_.PeriodPair.scale_lattice : (L.scale α).lattice = Submodule.map (mulLeftZ (α : ℂ)) L.lattice := by
  unfold lattice scale
  rw [Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, mulLeftZ_apply]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨L.ω₁, Or.inl rfl, rfl⟩
    · exact ⟨L.ω₂, Or.inr rfl, rfl⟩
  · rintro ⟨w, hw | hw, rfl⟩ <;> simp [hw]

p2m_export "PeriodPair" "scale_lattice"

private def _root_.PeriodPair.scaleLatticeEquiv : L.lattice ≃ₗ[ℤ] (L.scale α).lattice :=
  (Submodule.equivMapOfInjective (mulLeftZ (α : ℂ))
    (fun _ _ h => mul_left_cancel₀ α.ne_zero (by simpa using h)) L.lattice).trans
    (LinearEquiv.ofEq _ _ (L.scale_lattice α).symm)

p2m_export "PeriodPair" "scaleLatticeEquiv"
@[scoped simp] theorem scaleLatticeEquiv_apply (l : L.lattice) :
    ((L.scaleLatticeEquiv α l : (L.scale α).lattice) : ℂ) = (α : ℂ) * (l : ℂ) := rfl

end Scale
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section Homogeneity

variable (α : ℂˣ)

theorem G_scale (n : ℕ) : (L.scale α).G n = ((α : ℂ) ^ n)⁻¹ * L.G n := by
  unfold G
  rw [← (L.scaleLatticeEquiv α).toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, scaleLatticeEquiv_apply, mul_pow, mul_inv]
  exact tsum_mul_left

theorem g₂_scale : (L.scale α).g₂ = ((α : ℂ) ^ 4)⁻¹ * L.g₂ := by
  unfold g₂; rw [G_scale]; ring

theorem g₃_scale : (L.scale α).g₃ = ((α : ℂ) ^ 6)⁻¹ * L.g₃ := by
  unfold g₃; rw [G_scale]; ring

theorem discriminant_scale :
    (L.scale α).g₂ ^ 3 - 27 * (L.scale α).g₃ ^ 2
      = ((α : ℂ) ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [g₂_scale, g₃_scale]; ring

theorem discriminantNeZero_scale_iff :
    (L.scale α).DiscriminantNeZero ↔ L.DiscriminantNeZero := by
  unfold DiscriminantNeZero
  rw [discriminant_scale]
  simp only [mul_ne_zero_iff, and_iff_right (inv_ne_zero (pow_ne_zero 12 α.ne_zero))]

end Homogeneity
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

section LatticeDependence

variable {L L' : PeriodPair}

private def latticeEquivOfEq (h : L.lattice = L'.lattice) : L.lattice ≃ L'.lattice where
  toFun l := ⟨(l : ℂ), h ▸ l.2⟩
  invFun l := ⟨(l : ℂ), h.symm ▸ l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem G_eq_of_lattice_eq (h : L.lattice = L'.lattice) (n : ℕ) : L.G n = L'.G n :=
  (latticeEquivOfEq h).tsum_eq fun l => ((l : ℂ) ^ n)⁻¹

theorem g₂_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.g₂ = L'.g₂ := by
  unfold g₂; rw [G_eq_of_lattice_eq h]

theorem g₃_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.g₃ = L'.g₃ := by
  unfold g₃; rw [G_eq_of_lattice_eq h]

end LatticeDependence
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

end PeriodPair
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"
end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"

section
section

noncomputable section

open scoped UpperHalfPlane Real
p2m_open "Complex UpperHalfPlane ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm"

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ latticeEquivProd g₃ derivWeierstrassP_sq ω₂ indep latticeEquiv_symm_apply G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_zero IsUniformization jLattice JSurjective ofTau ofTau_lattice scale_indep scale scale_ω₁ scale_ω₂ sublatticeIndex"
p2m_open "PeriodPair"

theorem kw_discriminant_ofTau_eq (τ : ℍ) :
    (ofTau τ).g₂ ^ 3 - 27 * (ofTau τ).g₃ ^ 2
      = (64 * (π : ℂ) ^ 12 / 27) * (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  rw [kw_g₂_ofTau, kw_g₃_ofTau]; ring

theorem kw_discriminantNeZero_ofTau (τ : ℍ) : (ofTau τ).DiscriminantNeZero := by
  unfold DiscriminantNeZero
  rw [kw_discriminant_ofTau_eq]
  refine mul_ne_zero ?_ (sub_ne_zero.mpr (kw_E4cube_ne_E6sq τ))
  refine div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 12 ?_)) (by norm_num)
  exact_mod_cast Real.pi_ne_zero

theorem kw_discriminantNeZero_of_lattice_eq {L L' : PeriodPair}
    (h : L.lattice = L'.lattice) : L.DiscriminantNeZero ↔ L'.DiscriminantNeZero := by
  unfold DiscriminantNeZero
  rw [g₂_eq_of_lattice_eq h, g₃_eq_of_lattice_eq h]

theorem kw_im_div_ne_zero (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  have hω₂ : L.ω₂ ≠ 0 := by
    have := L.indep.ne_zero 1; simpa using this
  intro him

  have hdiv : (L.ω₁ / L.ω₂ : ℂ) = ((L.ω₁ / L.ω₂).re : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  have hreal : L.ω₁ = ((L.ω₁ / L.ω₂).re : ℂ) * L.ω₂ := by
    rw [← hdiv, div_mul_cancel₀ _ hω₂]
  have key : (1 : ℝ) • L.ω₁ + (-(L.ω₁ / L.ω₂).re) • L.ω₂ = 0 := by
    rw [one_smul, _root_.neg_smul, Complex.real_smul, ← hreal, add_neg_cancel]
  exact one_ne_zero (LinearIndependent.pair_iff.mp L.indep 1 (-(L.ω₁ / L.ω₂).re) key).1

theorem kw_span_neg_fst (a b : ℂ) :
    Submodule.span ℤ ({-a, b} : Set ℂ) = Submodule.span ℤ ({a, b} : Set ℂ) := by
  have hna : (-a : ℂ) ∈ Submodule.span ℤ ({a, b} : Set ℂ) :=
    neg_mem (Submodule.subset_span (Set.mem_insert _ _))
  have ha : (a : ℂ) ∈ Submodule.span ℤ ({-a, b} : Set ℂ) := by
    have hneg : (-(-a) : ℂ) ∈ Submodule.span ℤ ({-a, b} : Set ℂ) :=
      neg_mem (Submodule.subset_span (Set.mem_insert _ _))
    simpa using hneg
  apply le_antisymm <;> rw [Submodule.span_le, Set.insert_subset_iff] <;>
    exact ⟨by assumption,
      Set.singleton_subset_iff.mpr (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))⟩

private theorem _root_.PeriodPair.kw_discriminantNeZero (L : PeriodPair) : L.DiscriminantNeZero := by
  have hω₂ : L.ω₂ ≠ 0 := by have := L.indep.ne_zero 1; simpa using this
  set α : ℂˣ := (Units.mk0 L.ω₂ hω₂)⁻¹
  have hα : (α : ℂ) = (L.ω₂)⁻¹ := by
    simp only [α, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hω : (α : ℂ) * L.ω₁ = L.ω₁ / L.ω₂ ∧ (α : ℂ) * L.ω₂ = 1 := by
    refine ⟨?_, ?_⟩ <;> rw [hα] <;> field_simp

  have hlat : (L.scale α).lattice = Submodule.span ℤ {L.ω₁ / L.ω₂, 1} := by
    simp only [lattice, scale_ω₁, scale_ω₂, hω.1, hω.2]

  rcases lt_or_gt_of_ne (kw_im_div_ne_zero L) with hneg | hpos
  ·
    set τ : ℍ := ⟨-(L.ω₁ / L.ω₂), by simp only [Complex.neg_im]; linarith⟩
    have heq : (L.scale α).lattice = (ofTau τ).lattice := by
      rw [hlat, ofTau_lattice]; exact (kw_span_neg_fst _ _).symm
    exact (discriminantNeZero_scale_iff L α).mp
      ((kw_discriminantNeZero_of_lattice_eq heq).mpr (kw_discriminantNeZero_ofTau τ))
  ·
    set τ : ℍ := ⟨L.ω₁ / L.ω₂, hpos⟩
    have heq : (L.scale α).lattice = (ofTau τ).lattice := by rw [hlat, ofTau_lattice]
    exact (discriminantNeZero_scale_iff L α).mp
      ((kw_discriminantNeZero_of_lattice_eq heq).mpr (kw_discriminantNeZero_ofTau τ))

p2m_export "PeriodPair" "kw_discriminantNeZero"

end PeriodPair
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"
end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_discriminant_ne_zero.ModularForm P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair"

theorem solution (L : PeriodPair) : L.DiscriminantNeZero :=
  L.kw_discriminantNeZero

end S_PeriodPair_discriminant_ne_zero
end P2MW
export P2MW.S_PeriodPair_discriminant_ne_zero (solution)
