-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_smul_qmPeriodLattice_pair_eq_iff_exists_fuchsianGroup_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5ca30ae4-ab56-53b4-a035-dbe64c702773

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_isUnitOf_smul_eq_of_smul_qmPeriodLattice_eq
import Theorems.Thm_QuaternionAlgebra_denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq
import Theorems.Thm_CerednikDrinfeld_exists_isUnitOf_nrd_eq_one_of_mem_fuchsianGroup
import Theorems.Thm_QuaternionAlgebra_det_eq_nrd_of_injective
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_smul_qmPeriodLattice_pair_eq_iff_exists_fuchsianGroup_smul_eq

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace P1Orbit11

variable {a b : ℚ}

theorem nrd_mul (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [nrd, QuaternionAlgebra.mk_mul_mk]
  ring

theorem ne_zero_and_ne_zero {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q') :
    a ≠ 0 ∧ b ≠ 0 := by
  have key : ∀ y : ℍ[ℚ, a, b], y ≠ 0 → y * y = 0 → False := by
    intro y hy hyy
    obtain ⟨u, rfl⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB y hy
    apply hy
    calc (u : ℍ[ℚ, a, b]) = ↑u⁻¹ * (↑u * ↑u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [hyy, mul_zero]
  refine ⟨fun h0 => key ⟨0, 1, 0, 0⟩ ?_ ?_, fun h0 => key ⟨0, 0, 1, 0⟩ ?_ ?_⟩
  · intro h; simpa using congrArg QuaternionAlgebra.imI h
  · ext <;> simp [h0]
  · intro h; simpa using congrArg QuaternionAlgebra.imJ h
  · ext <;> simp [h0]

theorem nrd_eq_one_or_eq_neg_one_of_isUnitOf {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {u : ℍ[ℚ, a, b]}
    (hu : IsUnitOf Λ u) : nrd u = 1 ∨ nrd u = -1 := by
  obtain ⟨huΛ, v, hvΛ, huv, -⟩ := hu
  obtain ⟨m, hm⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd huΛ).1
  obtain ⟨n, hn⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hvΛ).1
  have h1 : nrd u * nrd v = 1 := by rw [← nrd_mul, huv, nrd_one]
  have hmn : m * n = 1 := by
    have : ((m * n : ℤ) : ℚ) = 1 := by push_cast; rw [hm, hn, h1]
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmn with h | h
  · left; rw [← hm, h]; norm_num
  · right; rw [← hm, h]; norm_num

end P1Orbit11

open P1Orbit11 in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (τ τ' : UpperHalfPlane) :
    (∃ c : ℂ, c ≠ 0 ∧ c • qmPeriodLattice ι Λ τ = qmPeriodLattice ι Λ τ' ∧ c • qmPeriodLattice ι J' τ = qmPeriodLattice ι J' τ') ↔
      ∃ γ ∈ fuchsianGroup R ι, γ • τ = τ' := by
  have hO : IsOrder Λ := hΛ.isOrder
  have hRO : IsOrder R := hR.isOrder
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero hB
  obtain ⟨-, -, -, -, hstabR⟩ := hJ'

  have hJ'R : ∀ u ∈ R, ∀ y ∈ J', y * u ∈ J' := fun u hu y hy => ((hstabR u (hRΛ hu)).1 hu) y hy
  have hJ'eq : ∀ u v : ℍ[ℚ, a, b], u ∈ R → v ∈ R → u * v = 1 → v * u = 1 →
      ∀ w : Fin 2 → ℂ, (∃ y ∈ J', qmPeriodMap ι τ (y * u) = w) ↔ w ∈ qmPeriodLattice ι J' τ := by
    intro u v hu hv huv hvu w
    rw [mem_qmPeriodLattice_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y * u, hJ'R u hu y hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y * v, hJ'R v hv y hy, by rw [mul_assoc, hvu, mul_one]⟩
  constructor
  · rintro ⟨c, hc, hcL, hcJ⟩
    obtain ⟨u, hu, g, hgu, hdet, hgτ, hcd⟩ :=
      QuaternionAlgebra.exists_isUnitOf_smul_eq_of_smul_qmPeriodLattice_eq ι hι Λ hO.one_mem τ τ' c hcL
    have hdetu : (ι u).det = ((nrd u : ℚ) : ℝ) := QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι u
    have hnrd : nrd u = 1 := by
      rcases nrd_eq_one_or_eq_neg_one_of_isUnitOf hO hu with h | h
      · exact h
      · exfalso
        have : (g : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by rw [hgu, hdetu, h]; push_cast; ring
        have h2 : g.det.val = (g : Matrix (Fin 2) (Fin 2) ℝ).det := Matrix.GeneralLinearGroup.val_det_apply g
        linarith
    obtain ⟨huΛ, v, hvΛ, huv, hvu⟩ := hu

    have hinj := (hO.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span ha hb ι τ).1
    have h2 := (QuaternionAlgebra.denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq ι J' u g hgu hdet τ).2.1
    have hd : UpperHalfPlane.denom g τ ≠ 0 := UpperHalfPlane.denom_ne_zero g τ
    have hc' : c = (UpperHalfPlane.denom g τ)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left hcd
    have hJτ : ∀ w : Fin 2 → ℂ, w ∈ qmPeriodLattice ι J' τ ↔ ∃ y ∈ J', qmPeriodMap ι τ (y * u) = w := by
      intro w
      rw [← h2, hgτ, ← hcJ, smul_smul, hc', mul_inv_cancel₀ hd, one_smul]
    have huR' : ∀ y ∈ J', y * u ∈ J' := by
      intro y hy
      have : qmPeriodMap ι τ (y * u) ∈ qmPeriodLattice ι J' τ := (hJτ _).2 ⟨y, hy, rfl⟩
      rw [mem_qmPeriodLattice_iff] at this
      obtain ⟨z, hz, hzy⟩ := this
      rwa [← hinj hzy]
    have hvR' : ∀ y ∈ J', y * v ∈ J' := by
      intro y hy
      have : qmPeriodMap ι τ (y * v) ∈ qmPeriodLattice ι J' τ := (mem_qmPeriodLattice_iff _ _ _ _).2 ⟨y * v, ?_, rfl⟩
      · exact (mem_qmPeriodLattice_iff _ _ _ _).1 this |>.elim fun z hz => by rw [← hinj hz.2]; exact hz.1
      ·
        have hmem : qmPeriodMap ι τ ((y * v) * u) ∈ qmPeriodLattice ι J' τ := by
          rw [mul_assoc, hvu, mul_one]; exact (mem_qmPeriodLattice_iff _ _ _ _).2 ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hzy⟩ := (hJτ _).1 hmem
        have := hinj hzy

        have : z = y * v := by
          have h' := congrArg (· * v) this
          simpa [mul_assoc, huv] using h'
        rw [← this]; exact hz
    have huR : u ∈ R := (hstabR u huΛ).2 huR'
    have hvR : v ∈ R := (hstabR v hvΛ).2 hvR'
    refine ⟨g, ?_, hgτ⟩
    let U : (ℍ[ℚ, a, b])ˣ := ⟨u, v, huv, hvu⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · refine Subgroup.mem_map.2 ⟨U, Subgroup.subset_closure ⟨huR, v, hvR, huv, hvu⟩, ?_⟩
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, hgu]
      rfl
    · rw [MonoidHom.mem_ker]
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgu, hdetu, hnrd]
      push_cast
      rfl
  · rintro ⟨γ, hγ, hγτ⟩
    obtain ⟨u, huR, hnrd, hγu⟩ :=
      CerednikDrinfeld.exists_isUnitOf_nrd_eq_one_of_mem_fuchsianGroup ha hb R hRO ι hι γ hγ
    obtain ⟨huR₀, v, hvR₀, huv, hvu⟩ := huR
    have huΛ : IsUnitOf Λ u := ⟨hRΛ huR₀, v, hRΛ hvR₀, huv, hvu⟩
    have hdet : 0 < γ.det.val := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hγu, QuaternionAlgebra.det_eq_nrd_of_injective ha hb ι hι u, hnrd]
      norm_num
    have hΛ3 := (QuaternionAlgebra.denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq ι Λ u γ hγu hdet τ).2.2
      (fun y z hy hz => hO.mul_mem hy hz) huΛ
    have hJ2 := (QuaternionAlgebra.denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq ι J' u γ hγu hdet τ).2.1
    have hd : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
    refine ⟨(UpperHalfPlane.denom γ τ)⁻¹, inv_ne_zero hd, ?_, ?_⟩
    · rw [← hγτ, ← hΛ3, smul_smul, inv_mul_cancel₀ hd, one_smul]
    · have hJ3 : UpperHalfPlane.denom γ τ • qmPeriodLattice ι J' (γ • τ) = qmPeriodLattice ι J' τ := by
        ext w; rw [hJ2 w]; exact hJ'eq u v huR₀ hvR₀ huv hvu w
      rw [← hγτ, ← hJ3, smul_smul, inv_mul_cancel₀ hd, one_smul]

end S_QuaternionAlgebra_IsEichlerOrder_exists_smul_qmPeriodLattice_pair_eq_iff_exists_fuchsianGroup_smul_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_smul_qmPeriodLattice_pair_eq_iff_exists_fuchsianGroup_smul_eq (solution)
