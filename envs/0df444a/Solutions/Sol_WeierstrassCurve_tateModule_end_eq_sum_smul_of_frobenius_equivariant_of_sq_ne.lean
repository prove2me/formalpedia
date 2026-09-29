-- Prove2me | solution 1 for WeierstrassCurve.tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/38a55190-4f03-5d15-ba8c-8ea99cef990f

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_trace_frobenius_tateModule_eq_card_add_one_sub
import Theorems.Thm_WeierstrassCurve_det_frobenius_tateModule_eq_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two FrobeniusEndo.linePencil_apply WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace TateEndSpan

section MapT

variable {p : ℕ} [Fact p.Prime] {M M' : Type} [AddCommGroup M] [AddCommGroup M']

noncomputable def mapT (f : M →+ M') : TateModule p M →ₗ[ℤ_[p]] TateModule p M' where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, _root_.map_zero],
      by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    change f ((x : ℕ → M) n + (y : ℕ → M) n) = f ((x : ℕ → M) n) + f ((y : ℕ → M) n)
    exact map_add f _ _)
  map_smul' a x := Subtype.ext (funext fun n => by
    change f (((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → M) n)
    exact map_zsmul f _ _)

@[scoped simp] theorem mapT_apply (f : M →+ M') (x : TateModule p M) (n : ℕ) :
    ((mapT (p := p) f x : TateModule p M') : ℕ → M') n = f ((x : ℕ → M) n) := rfl

theorem mapT_zero : mapT (p := p) (0 : M →+ M') = 0 :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

theorem mapT_add (f g : M →+ M') : mapT (p := p) (f + g) = mapT (p := p) f + mapT (p := p) g :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

theorem mapT_id : mapT (p := p) (AddMonoidHom.id M) = LinearMap.id :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

noncomputable def mapTHom : (M →+ M') →+ (TateModule p M →ₗ[ℤ_[p]] TateModule p M') where
  toFun := mapT (p := p)
  map_zero' := mapT_zero
  map_add' := mapT_add

theorem mapT_sum {ι : Type*} (s : Finset ι) (f : ι → (M →+ M')) :
    mapT (p := p) (∑ i ∈ s, f i) = ∑ i ∈ s, mapT (p := p) (f i) :=
  map_sum (mapTHom (p := p)) f s

theorem mapT_nsmul (a : ℕ) (f : M →+ M') :
    mapT (p := p) (a • f) = (a : ℤ_[p]) • mapT (p := p) f := by
  rw [Nat.cast_smul_eq_nsmul]
  exact map_nsmul (mapTHom (p := p)) a f

theorem eq_zero_of_p_smul_eq_zero (y : TateModule p M) (hy : (p : ℤ_[p]) • y = 0) : y = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have h : ((((p : ℕ) : ℤ_[p]) • y : TateModule p M) : ℕ → M) (n + 1) = 0 := by
    rw [hy]; rfl
  rw [TateModule.natCast_padicInt_smul_apply, TateModule.compat] at h
  rw [h]; rfl

theorem eq_zero_of_pow_smul_eq_zero (N : ℕ) (y : TateModule p M)
    (hy : (p : ℤ_[p]) ^ N • y = 0) : y = 0 := by
  induction N generalizing y with
  | zero => rwa [pow_zero, one_smul] at hy
  | succ N ih =>
    rw [pow_succ, mul_smul] at hy
    exact eq_zero_of_p_smul_eq_zero y (ih _ hy)

end MapT

section Descent

variable {p : ℕ} [Fact p.Prime] {M M' : Type} [AddCommGroup M] [AddCommGroup M']

noncomputable def spanT (S : Set (M →+ M')) :
    Submodule ℤ_[p] (TateModule p M →ₗ[ℤ_[p]] TateModule p M') :=
  Submodule.span ℤ_[p] (mapT (p := p) '' S)

theorem mapT_mem_spanT (S : Set (M →+ M')) {α : M →+ M'} (hα : α ∈ S) :
    mapT (p := p) α ∈ spanT (p := p) S :=
  Submodule.subset_span ⟨α, hα, rfl⟩

theorem exists_of_mem_spanT (S : Set (M →+ M')) {Ψ : TateModule p M →ₗ[ℤ_[p]] TateModule p M'}
    (hΨ : Ψ ∈ spanT (p := p) S) :
    ∃ (n : ℕ) (c : Fin n → ℤ_[p]) (α : Fin n → (M →+ M')),
      (∀ i, α i ∈ S) ∧ ∑ i, c i • mapT (p := p) (α i) = Ψ := by
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp hΨ
  have hg' : ∀ i, ∃ α ∈ S, mapT (p := p) α = (g i : _) := fun i => (g i).2
  choose α hαS hαg using hg'
  refine ⟨n, c, α, hαS, ?_⟩
  rw [← hg]
  exact Finset.sum_congr rfl fun i _ => by rw [hαg]

variable {S : Set (M →+ M')}

theorem nsmul_mem_of_add_mem (hadd : ∀ {α β : M →+ M'}, α ∈ S → β ∈ S → α + β ∈ S)
    (hzero : (0 : M →+ M') ∈ S) {α : M →+ M'} (hα : α ∈ S) (a : ℕ) : a • α ∈ S := by
  induction a with
  | zero => rwa [zero_smul]
  | succ a ih => rw [succ_nsmul]; exact hadd ih hα

theorem sum_mem_of_add_mem (hadd : ∀ {α β : M →+ M'}, α ∈ S → β ∈ S → α + β ∈ S)
    (hzero : (0 : M →+ M') ∈ S) {ι : Type*} (s : Finset ι) (f : ι → (M →+ M'))
    (hf : ∀ i ∈ s, f i ∈ S) : ∑ i ∈ s, f i ∈ S :=
  Finset.sum_induction f (· ∈ S) (fun _ _ ha hb => hadd ha hb) hzero hf

theorem mem_spanT_of_p_smul_mem
    (hadd : ∀ {α β : M →+ M'}, α ∈ S → β ∈ S → α + β ∈ S) (hzero : (0 : M →+ M') ∈ S)
    (hsat : ∀ α ∈ S, (∀ P : M, ((p : ℕ) : ℤ) • P = 0 → α P = 0) →
      ∃ β ∈ S, ∀ P, α P = ((p : ℕ) : ℤ) • β P)
    (hlift : ∀ P : M, ((p : ℕ) : ℤ) • P = 0 → ∃ x : TateModule p M, (x : ℕ → M) 1 = P)
    {Ψ : TateModule p M →ₗ[ℤ_[p]] TateModule p M'}
    (hΨ : (p : ℤ_[p]) • Ψ ∈ spanT (p := p) S) : Ψ ∈ spanT (p := p) S := by
  obtain ⟨n, c, α, hαS, hsum⟩ := exists_of_mem_spanT S hΨ

  let a : Fin n → ℕ := fun i => (c i).appr 1
  have hd : ∀ i, ∃ d : ℤ_[p], c i = (a i : ℤ_[p]) + (p : ℤ_[p]) * d := by
    intro i
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec 1 (c i))
    refine ⟨d, ?_⟩
    rw [pow_one] at hd
    rw [mul_comm, hd]
    ring
  choose d hd using hd

  have hβS : (∑ i, a i • α i) ∈ S :=
    sum_mem_of_add_mem hadd hzero _ _ fun i _ => nsmul_mem_of_add_mem hadd hzero (hαS i) (a i)

  have hTβ : mapT (p := p) (∑ i, a i • α i)
      = (p : ℤ_[p]) • (Ψ - ∑ i, d i • mapT (p := p) (α i)) := by
    rw [smul_sub, ← hsum, Finset.smul_sum, mapT_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mapT_nsmul, hd i, add_smul, mul_smul, add_sub_cancel_right]

  have hker : ∀ P : M, ((p : ℕ) : ℤ) • P = 0 → (∑ i, a i • α i) P = 0 := by
    intro P hP
    obtain ⟨x, hx⟩ := hlift P hP
    have h1 : ((mapT (p := p) (∑ i, a i • α i) x : TateModule p M') : ℕ → M') 1
        = (∑ i, a i • α i) P := by
      rw [mapT_apply, hx]
    rw [← h1, hTβ, LinearMap.smul_apply, TateModule.natCast_padicInt_smul_apply]
    have := TateModule.torsion ((Ψ - ∑ i, d i • mapT (p := p) (α i)) x) 1
    rwa [pow_one] at this

  obtain ⟨β', hβ'S, hβ'⟩ := hsat _ hβS hker
  have hTβ' : mapT (p := p) (∑ i, a i • α i) = (p : ℤ_[p]) • mapT (p := p) β' := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun m => ?_)
    rw [mapT_apply, hβ', LinearMap.smul_apply, TateModule.natCast_padicInt_smul_apply, mapT_apply]

  have hzero' : (p : ℤ_[p]) • (Ψ - ∑ i, d i • mapT (p := p) (α i) - mapT (p := p) β') = 0 := by
    rw [smul_sub, ← hTβ, ← hTβ', sub_self]
  have hΨeq : Ψ = ∑ i, d i • mapT (p := p) (α i) + mapT (p := p) β' := by
    have h0 : Ψ - ∑ i, d i • mapT (p := p) (α i) - mapT (p := p) β' = 0 := by
      refine LinearMap.ext fun x => ?_
      have hx := LinearMap.congr_fun hzero' x
      rw [LinearMap.smul_apply, LinearMap.zero_apply] at hx
      rw [LinearMap.zero_apply]
      exact eq_zero_of_p_smul_eq_zero _ hx
    rwa [sub_sub, sub_eq_zero] at h0
  rw [hΨeq]
  exact Submodule.add_mem _
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mapT_mem_spanT S (hαS i)))
    (mapT_mem_spanT S hβ'S)

theorem mem_spanT_of_pow_smul_mem
    (hadd : ∀ {α β : M →+ M'}, α ∈ S → β ∈ S → α + β ∈ S) (hzero : (0 : M →+ M') ∈ S)
    (hsat : ∀ α ∈ S, (∀ P : M, ((p : ℕ) : ℤ) • P = 0 → α P = 0) →
      ∃ β ∈ S, ∀ P, α P = ((p : ℕ) : ℤ) • β P)
    (hlift : ∀ P : M, ((p : ℕ) : ℤ) • P = 0 → ∃ x : TateModule p M, (x : ℕ → M) 1 = P)
    (N : ℕ) {Ψ : TateModule p M →ₗ[ℤ_[p]] TateModule p M'}
    (hΨ : (p : ℤ_[p]) ^ N • Ψ ∈ spanT (p := p) S) : Ψ ∈ spanT (p := p) S := by
  induction N generalizing Ψ with
  | zero => rwa [pow_zero, one_smul] at hΨ
  | succ N ih =>
    rw [pow_succ', mul_smul] at hΨ
    exact ih (mem_spanT_of_p_smul_mem hadd hzero hsat hlift hΨ)

theorem mem_spanT_of_smul_mem
    (hadd : ∀ {α β : M →+ M'}, α ∈ S → β ∈ S → α + β ∈ S) (hzero : (0 : M →+ M') ∈ S)
    (hsat : ∀ α ∈ S, (∀ P : M, ((p : ℕ) : ℤ) • P = 0 → α P = 0) →
      ∃ β ∈ S, ∀ P, α P = ((p : ℕ) : ℤ) • β P)
    (hlift : ∀ P : M, ((p : ℕ) : ℤ) • P = 0 → ∃ x : TateModule p M, (x : ℕ → M) 1 = P)
    {c : ℤ_[p]} (hc : c ≠ 0) {Ψ : TateModule p M →ₗ[ℤ_[p]] TateModule p M'}
    (hΨ : c • Ψ ∈ spanT (p := p) S) : Ψ ∈ spanT (p := p) S := by
  refine mem_spanT_of_pow_smul_mem hadd hzero hsat hlift c.valuation ?_
  have hu := PadicInt.unitCoeff_spec hc
  have h2 : ((PadicInt.unitCoeff hc)⁻¹ : ℤ_[p]ˣ).val * c
      = ((PadicInt.unitCoeff hc)⁻¹ : ℤ_[p]ˣ).val
          * ((PadicInt.unitCoeff hc).val * (p : ℤ_[p]) ^ c.valuation) :=
    congrArg (((PadicInt.unitCoeff hc)⁻¹ : ℤ_[p]ˣ).val * ·) hu
  rw [← mul_assoc, Units.inv_mul, one_mul] at h2
  rw [← h2, mul_smul]
  exact Submodule.smul_mem _ _ hΨ

end Descent

section TwoByTwo

variable {R : Type*} [CommRing R]

omit [CommRing R] in
theorem ext_fin_two {A B : Matrix (Fin 2) (Fin 2) R} (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  rw [Matrix.eta_fin_two A, Matrix.eta_fin_two B, h00, h01, h10, h11]

theorem smul_eq_of_entries {c a b : R} {A P : Matrix (Fin 2) (Fin 2) R}
    (h00 : c * A 0 0 = a + b * P 0 0) (h01 : c * A 0 1 = b * P 0 1)
    (h10 : c * A 1 0 = b * P 1 0) (h11 : c * A 1 1 = a + b * P 1 1) :
    c • A = a • (1 : Matrix (Fin 2) (Fin 2) R) + b • P := by
  have h01' : (1 : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have h10' : (1 : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  refine ext_fin_two ?_ ?_ ?_ ?_
  · rw [Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one]
    exact h00
  · rw [Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      h01', smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
    exact h01
  · rw [Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      h10', smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
    exact h10
  · rw [Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one]
    exact h11

theorem exists_smul_eq_of_commute_fin_two [IsDomain R] (P A : Matrix (Fin 2) (Fin 2) R)
    (h : A * P = P * A) (hP : (Matrix.trace P) ^ 2 ≠ 4 * P.det) :
    ∃ c a b : R, c ≠ 0 ∧ c • A = a • (1 : Matrix (Fin 2) (Fin 2) R) + b • P := by
  have e : ∀ i j, A i 0 * P 0 j + A i 1 * P 1 j = P i 0 * A 0 j + P i 1 * A 1 j := by
    intro i j
    have := congrFun (congrFun h i) j
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  by_cases h01 : P 0 1 = 0
  · by_cases h10 : P 1 0 = 0
    ·
      have hd : P 0 0 - P 1 1 ≠ 0 := by
        intro hd
        apply hP
        rw [Matrix.trace_fin_two, Matrix.det_fin_two, h01, h10, sub_eq_zero.mp hd]
        ring
      have hA01 : A 0 1 = 0 := by
        have : A 0 1 * (P 0 0 - P 1 1) = 0 := by
          linear_combination -e01 + (A 0 0 - A 1 1) * h01
        exact (mul_eq_zero.mp this).resolve_right hd
      have hA10 : A 1 0 = 0 := by
        have : A 1 0 * (P 0 0 - P 1 1) = 0 := by
          linear_combination e10 + (A 0 0 - A 1 1) * h10
        exact (mul_eq_zero.mp this).resolve_right hd
      refine ⟨P 0 0 - P 1 1, A 1 1 * P 0 0 - P 1 1 * A 0 0, A 0 0 - A 1 1, hd,
        smul_eq_of_entries ?_ ?_ ?_ ?_⟩
      · ring
      · rw [hA01, h01]; ring
      · rw [hA10, h10]; ring
      · ring
    ·
      refine ⟨P 1 0, P 1 0 * A 1 1 - A 1 0 * P 1 1, A 1 0, h10, smul_eq_of_entries ?_ ?_ ?_ ?_⟩
      · linear_combination -e10
      · linear_combination -e11
      · ring
      · ring
  ·
    refine ⟨P 0 1, P 0 1 * A 0 0 - A 0 1 * P 0 0, A 0 1, h01, smul_eq_of_entries ?_ ?_ ?_ ?_⟩
    · ring
    · ring
    · linear_combination -e00
    · linear_combination -e01

theorem exists_smul_eq_of_comm [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (h2 : Module.finrank R M = 2) (π f : M →ₗ[R] M)
    (hcomm : f ∘ₗ π = π ∘ₗ f) (hdisc : (LinearMap.trace R M π) ^ 2 ≠ 4 * LinearMap.det π) :
    ∃ c a b : R, c ≠ 0 ∧ c • f = a • LinearMap.id + b • π := by
  let bs := Module.finBasisOfFinrankEq R M h2
  have hM : LinearMap.toMatrix bs bs f * LinearMap.toMatrix bs bs π
      = LinearMap.toMatrix bs bs π * LinearMap.toMatrix bs bs f := by
    rw [← LinearMap.toMatrix_comp bs bs bs, ← LinearMap.toMatrix_comp bs bs bs, hcomm]
  have hP : (Matrix.trace (LinearMap.toMatrix bs bs π)) ^ 2 ≠ 4 * (LinearMap.toMatrix bs bs π).det := by
    rwa [← LinearMap.trace_eq_matrix_trace R bs, LinearMap.det_toMatrix bs]
  obtain ⟨c, a, b, hc, e⟩ := exists_smul_eq_of_commute_fin_two _ _ hM hP
  refine ⟨c, a, b, hc, (LinearMap.toMatrix bs bs).injective ?_⟩
  rw [LinearEquiv.map_smul, LinearEquiv.map_add, LinearEquiv.map_smul, LinearEquiv.map_smul,
    LinearMap.toMatrix_id, e]

end TwoByTwo

end TateEndSpan
p2m_reactivate "P2MW.S_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne.TateEndSpan"

open TateEndSpan in
theorem solution {F : Type*} [Field F] [Fintype F] {k : Type} [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : F) ≠ 0) (ht : ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≠ 4 * (Fintype.card F : ℤ)) (Φ : TateModule ℓ (W⁄k).Point →ₗ[ℤ_[ℓ]] TateModule ℓ (W⁄k).Point) (hΦ : Φ ∘ₗ TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ = TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ ∘ₗ Φ) : ∃ (m : ℕ) (α : Fin m → ((W⁄k).Point →+ (W⁄k).Point)) (c : Fin m → ℤ_[ℓ]) (Ψ : Fin m → (TateModule ℓ (W⁄k).Point →ₗ[ℤ_[ℓ]] TateModule ℓ (W⁄k).Point)), (∀ j, α j ∈ WeierstrassCurve.rationalHomSet k W W) ∧ (∀ j (x : TateModule ℓ (W⁄k).Point) (n : ℕ), ((Ψ j x : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n = α j ((x : ℕ → (W⁄k).Point) n)) ∧ Φ = ∑ j, c j • Ψ j := by

  suffices hmem : Φ ∈ spanT (p := ℓ) (rationalHomSet k W W) by
    obtain ⟨n, c, α, hαS, hsum⟩ := exists_of_mem_spanT _ hmem
    exact ⟨n, α, c, fun j => mapT (p := ℓ) (α j), hαS, fun j x m => rfl, hsum.symm⟩

  have hℓk : (ℓ : k) ≠ 0 := by
    rw [← map_natCast (algebraMap F k)]
    exact (_root_.map_ne_zero _).mpr hℓ
  have hc : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ (W⁄k).Point ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ 2 :=
    fun n => WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓk)
  haveI := TateModule.free hc
  haveI := TateModule.finite hc

  have hadd : ∀ {α β : (W⁄k).Point →+ (W⁄k).Point}, α ∈ rationalHomSet k W W →
      β ∈ rationalHomSet k W W → α + β ∈ rationalHomSet k W W :=
    fun hα hβ => WeierstrassCurve.add_mem_rationalHomSet k W W hα hβ
  have hzero : (0 : (W⁄k).Point →+ (W⁄k).Point) ∈ rationalHomSet k W W :=
    zero_mem_rationalHomSet k W W
  have hsat : ∀ α ∈ rationalHomSet k W W,
      (∀ P : (W⁄k).Point, ((ℓ : ℕ) : ℤ) • P = 0 → α P = 0) →
        ∃ β ∈ rationalHomSet k W W, ∀ P, α P = ((ℓ : ℕ) : ℤ) • β P :=
    fun α hα hker =>
      WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero k W W hℓ hα hker
  have hlift : ∀ P : (W⁄k).Point, ((ℓ : ℕ) : ℤ) • P = 0 →
      ∃ x : TateModule ℓ (W⁄k).Point, (x : ℕ → (W⁄k).Point) 1 = P := by
    intro P hP
    obtain ⟨x, hx⟩ := TateModule.proj_surjective hc 1 P
      (TateModule.mem_torsionBy_one_of_smul_eq_zero hP)
    exact ⟨x, hx⟩

  have hT := WeierstrassCurve.trace_frobenius_tateModule_eq_card_add_one_sub W σ hσ ℓ hℓ
  have hD := WeierstrassCurve.det_frobenius_tateModule_eq_card W σ hσ ℓ hℓ
  obtain ⟨t, ht'⟩ : ∃ t : ℤ, t = (Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) :=
    ⟨_, rfl⟩
  rw [← ht'] at hT ht
  set π := TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ with hπ
  have hdisc : (LinearMap.trace ℤ_[ℓ] (TateModule ℓ (W⁄k).Point) π) ^ 2 ≠ 4 * LinearMap.det π := by
    rw [hT, hD]
    intro h
    apply ht
    have h' : ((t ^ 2 : ℤ) : ℤ_[ℓ]) = ((4 * (Fintype.card F : ℤ) : ℤ) : ℤ_[ℓ]) := by
      rw [Int.cast_pow, Int.cast_mul, Int.cast_natCast, h]
      norm_num
    exact Int.cast_injective h'

  obtain ⟨c, a, b, hc0, e⟩ :=
    exists_smul_eq_of_comm (TateModule.finrank_eq_two hc) π Φ hΦ hdisc

  have h1 : (LinearMap.id : TateModule ℓ (W⁄k).Point →ₗ[ℤ_[ℓ]] TateModule ℓ (W⁄k).Point)
      ∈ spanT (p := ℓ) (rationalHomSet k W W) := by
    rw [← mapT_id]
    exact mapT_mem_spanT _ (id_mem_rationalHomSet k W)
  have h2 : π ∈ spanT (p := ℓ) (rationalHomSet k W W) := by
    have hπT : π = mapT (p := ℓ) (Point.map (W' := W) σ.toAlgHom) :=
      LinearMap.ext fun x => Subtype.ext (funext fun n => rfl)
    rw [hπT]
    exact mapT_mem_spanT _
      (Or.inr (isRationallyRepresented_map_of_pow k W σ.toAlgHom (Fintype.card F) fun x => hσ x))

  refine mem_spanT_of_smul_mem hadd hzero hsat hlift hc0 ?_
  rw [e]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

end S_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne
end P2MW
export P2MW.S_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne (solution)
