-- Prove2me | solution 1 for PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/dc38fb07-6c13-5403-b97b-d22713546f4a

import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_PeriodPair_discriminant_ne_zero
import Theorems.Thm_PeriodPair_isUniformization_toPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ mk latticeEquivProd g₃ derivWeierstrassP_sq ω₂ G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero IsUniformization jLattice JSurjective ofTau scale_indep scale sublatticeIndex discriminant_ne_zero isUniformization_toPoint"
p2m_open "PeriodPair"

private theorem _root_.PeriodPair.kw_toPoint_add (L : PeriodPair) (hD : L.DiscriminantNeZero) (z w : ℂ) :
    L.toPoint hD (z + w) = L.toPoint hD z + L.toPoint hD w :=
  (PeriodPair.isUniformization_toPoint L hD).1 z w
p2m_export "PeriodPair" "kw_toPoint_add"

private theorem _root_.PeriodPair.kw_isUniformization (L : PeriodPair) : L.IsUniformization L.discriminant_ne_zero :=
  PeriodPair.isUniformization_toPoint L _
p2m_export "PeriodPair" "kw_isUniformization"
end PeriodPair

namespace AlgebraicCurve
end AlgebraicCurve
namespace Complex
p2m_export "Complex" "re lift finrank_real_complex arg exists exp mk ext I"
p2m_open "Complex"
end Complex
namespace Filter
p2m_export "Filter" "ker mk cocountable mem_ker mem_map unique map"
p2m_open "Filter"
end Filter
namespace LinearAlgebra
namespace Projectivization
p2m_open "LinearAlgebra.Projectivization LinearAlgebra"
end LinearAlgebra.Projectivization
namespace ModularCurve
end ModularCurve
namespace Module
p2m_export "Module" "Injective equiv Finite.equiv finrank Free mk Dual Free.of_equiv End restrictScalars"
p2m_open "Module"
end Module
namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ mk latticeEquivProd g₃ derivWeierstrassP_sq ω₂ G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero IsUniformization jLattice JSurjective ofTau scale_indep scale sublatticeIndex discriminant_ne_zero isUniformization_toPoint"
p2m_open "PeriodPair"
end PeriodPair
namespace Polynomial
p2m_export "Polynomial" "C X unique aeval ext_iff degree factor map roots sum infinite reverse nontrivial flt coe_zero module coe_add div mod ext content ring lifts restriction"
p2m_open "Polynomial"
end Polynomial
namespace Set
p2m_export "Set" "image ext unit mem_singleton_iff mem_image integer mem_insert_iff inclusion range"
p2m_open "Set"
end Set
namespace UpperHalfPlane
p2m_export "UpperHalfPlane" "σ ne_zero I J mk coe_mk re"
p2m_open "UpperHalfPlane"
end UpperHalfPlane
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ exists_variableChange_of_j_eq reduction toAffine Δ c₄ j"
p2m_open "WeierstrassCurve"
end WeierstrassCurve
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ exists_variableChange_of_j_eq reduction toAffine Δ c₄ j"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "map Point polynomial"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"
end WeierstrassCurve.Affine

section
section

p2m_open "Complex P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.Complex Filter P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.Filter Set P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.Set"

p2m_open_scoped "PeriodPair P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ mk latticeEquivProd g₃ derivWeierstrassP_sq ω₂ G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero IsUniformization jLattice JSurjective ofTau scale_indep scale sublatticeIndex discriminant_ne_zero isUniformization_toPoint"
p2m_open "PeriodPair"

variable (L : PeriodPair)

section Liouville

end Liouville

section Curve

end Curve

section HalfPeriods

end HalfPeriods

section ToPoint

end ToPoint

section JInvariant

end JInvariant

section Isogeny

end Isogeny

end PeriodPair

namespace Projectivization
p2m_export "Projectivization" "mk map card"
p2m_open "Projectivization"

p2m_open_scoped "LinearAlgebra.Projectivization P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.LinearAlgebra.Projectivization"

end Projectivization
end

end

section
section

set_option maxHeartbeats 6400000

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.WeierstrassCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.AlgebraicCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

namespace ModularCurve

section IntersectionEngine

namespace MilneI72IntersectionData

end MilneI72IntersectionData

end IntersectionEngine

section LatticeQuotient

variable {V : Type*} [AddCommGroup V] [DivisibleBy V ℤ] [NoZeroSMulDivisors ℤ V]

def divNHom (n : ℤ) (hn : n ≠ 0) : V →+ V where
  toFun v := DivisibleBy.div v n
  map_zero' := smul_right_injective V hn (by
    show n • DivisibleBy.div (0 : V) n = n • 0
    rw [DivisibleBy.div_cancel _ hn, smul_zero])
  map_add' a b := smul_right_injective V hn (by
    show n • DivisibleBy.div (a + b) n = n • (DivisibleBy.div a n + DivisibleBy.div b n)
    rw [smul_add, DivisibleBy.div_cancel _ hn, DivisibleBy.div_cancel _ hn,
      DivisibleBy.div_cancel _ hn])

@[scoped simp] theorem smul_divNHom (n : ℤ) (hn : n ≠ 0) (v : V) :
    n • divNHom n hn v = v :=
  DivisibleBy.div_cancel v hn

theorem divNHom_smul (n : ℤ) (hn : n ≠ 0) (v : V) :
    divNHom n hn (n • v) = v :=
  smul_right_injective V hn
    (show n • divNHom n hn (n • v) = n • v from smul_divNHom n hn (n • v))

variable (Λ : AddSubgroup V) {n : ℕ}

def latticeDivQuot (hn : (n : ℤ) ≠ 0) :
    ↥Λ →+ Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ) where
  toFun w := ⟨QuotientAddGroup.mk (divNHom (n : ℤ) hn (w : V)), by
    rw [Submodule.mem_torsionBy_iff]
    show (n : ℤ) • (QuotientAddGroup.mk (divNHom (n : ℤ) hn (w : V)) : V ⧸ Λ) = 0
    rw [← QuotientAddGroup.mk_zsmul, smul_divNHom]
    exact (QuotientAddGroup.eq_zero_iff _).mpr w.2⟩
  map_zero' := by
    apply Subtype.ext
    show (QuotientAddGroup.mk (divNHom (n : ℤ) hn ((0 : ↥Λ) : V)) : V ⧸ Λ) = 0
    simp
  map_add' a b := by
    apply Subtype.ext
    show (QuotientAddGroup.mk (divNHom (n : ℤ) hn (((a + b : ↥Λ)) : V)) : V ⧸ Λ)
        = QuotientAddGroup.mk (divNHom (n : ℤ) hn (a : V))
          + QuotientAddGroup.mk (divNHom (n : ℤ) hn (b : V))
    push_cast
    rw [map_add, QuotientAddGroup.mk_add]

@[scoped simp] theorem coe_latticeDivQuot (hn : (n : ℤ) ≠ 0) (w : ↥Λ) :
    ((latticeDivQuot Λ hn w : Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ)) : V ⧸ Λ)
      = QuotientAddGroup.mk (divNHom (n : ℤ) hn (w : V)) :=
  rfl

theorem latticeDivQuot_surjective (hn : (n : ℤ) ≠ 0) :
    Function.Surjective (latticeDivQuot Λ hn) := by
  rintro ⟨x, hx⟩
  rw [Submodule.mem_torsionBy_iff] at hx

  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x

  have hvΛ : (n : ℤ) • v ∈ Λ := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_zsmul]
    exact hx
  refine ⟨⟨(n : ℤ) • v, hvΛ⟩, Subtype.ext ?_⟩
  rw [coe_latticeDivQuot]
  show (QuotientAddGroup.mk (divNHom (n : ℤ) hn ((n : ℤ) • v)) : V ⧸ Λ)
      = QuotientAddGroup.mk v
  rw [divNHom_smul]

theorem mem_ker_latticeDivQuot (hn : (n : ℤ) ≠ 0) (w : ↥Λ) :
    w ∈ (latticeDivQuot Λ hn).ker
      ↔ w ∈ LinearMap.range (LinearMap.lsmul ℤ ↥Λ (n : ℤ)) := by
  constructor
  · intro hker
    rw [AddMonoidHom.mem_ker] at hker
    have hcoe : ((latticeDivQuot Λ hn w :
        Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ)) : V ⧸ Λ) = 0 := by
      rw [hker]; rfl
    rw [coe_latticeDivQuot, QuotientAddGroup.eq_zero_iff] at hcoe

    refine ⟨⟨divNHom (n : ℤ) hn (w : V), hcoe⟩, ?_⟩
    apply Subtype.ext
    show (n : ℤ) • divNHom (n : ℤ) hn (w : V) = (w : V)
    exact smul_divNHom (n : ℤ) hn (w : V)
  · rintro ⟨μ, rfl⟩
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    rw [coe_latticeDivQuot]
    show (QuotientAddGroup.mk (divNHom (n : ℤ) hn ((n : ℤ) • (μ : V))) : V ⧸ Λ) = 0
    rw [divNHom_smul, QuotientAddGroup.eq_zero_iff]
    exact μ.2

theorem ker_latticeDivQuot (hn : (n : ℤ) ≠ 0) :
    (latticeDivQuot Λ hn).ker
      = (LinearMap.range (LinearMap.lsmul ℤ ↥Λ (n : ℤ))).toAddSubgroup := by
  ext w
  exact mem_ker_latticeDivQuot Λ hn w

def latticeQuotTorsionEquiv (hn : (n : ℤ) ≠ 0) :
    ModN ↥Λ n ≃+ Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ) := by

  refine AddEquiv.ofBijective
    (QuotientAddGroup.lift _ (latticeDivQuot Λ hn) ?_) ⟨?_, ?_⟩
  ·
    intro w hw
    have : w ∈ (latticeDivQuot Λ hn).ker := by
      rw [ker_latticeDivQuot]; exact hw
    exact this
  ·
    rintro ⟨a⟩ ⟨b⟩ hab
    refine (Submodule.Quotient.eq _).mpr ?_

    have hker : a - b ∈ (latticeDivQuot Λ hn).ker := by
      rw [AddMonoidHom.mem_ker, map_sub]
      exact sub_eq_zero.mpr hab
    rwa [ker_latticeDivQuot] at hker
  ·
    intro y
    obtain ⟨w, hw⟩ := latticeDivQuot_surjective Λ hn y
    exact ⟨QuotientAddGroup.mk w, hw⟩

theorem card_torsionBy_latticeQuotient [Module.Free ℤ ↥Λ] [Module.Finite ℤ ↥Λ]
    (hn : (n : ℤ) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ)) = n ^ Module.finrank ℤ ↥Λ := by
  haveI : NeZero n := ⟨by exact_mod_cast hn⟩
  rw [← Nat.card_congr (latticeQuotTorsionEquiv Λ hn).toEquiv, ModN.natCard_eq]

end LatticeQuotient

section Producer

variable {N p : ℕ}
variable {V : Type*} [AddCommGroup V] [DivisibleBy V ℤ] [NoZeroSMulDivisors ℤ V]
variable {Λ : AddSubgroup V} [Module.Free ℤ ↥Λ] [Module.Finite ℤ ↥Λ]

end Producer

end ModularCurve
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"
end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

section
section

noncomputable section

p2m_open_scoped "PeriodPair P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

p2m_open "WeierstrassCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.WeierstrassCurve.Affine P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve Polynomial P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.Polynomial"

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ mk latticeEquivProd g₃ derivWeierstrassP_sq ω₂ G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero IsUniformization jLattice JSurjective ofTau scale_indep scale sublatticeIndex discriminant_ne_zero isUniformization_toPoint"
p2m_open "PeriodPair"

variable (L : PeriodPair)

private def _root_.PeriodPair.kw_toPointHom : ℂ →+ (L.weierstrassCurve.toAffine).Point where
  toFun := L.toPoint L.discriminant_ne_zero
  map_zero' := L.toPoint_zero L.discriminant_ne_zero
  map_add' := L.kw_toPoint_add L.discriminant_ne_zero

p2m_export "PeriodPair" "kw_toPointHom"
private theorem _root_.PeriodPair.kw_toPointHom_apply (z : ℂ) :
    L.kw_toPointHom z = L.toPoint L.discriminant_ne_zero z := rfl

p2m_export "PeriodPair" "kw_toPointHom_apply"

private theorem _root_.PeriodPair.kw_ker_toPointHom :
    L.kw_toPointHom.ker = L.lattice.toAddSubgroup := by
  ext z
  constructor
  · exact fun hz => (L.kw_isUniformization).2.2 z hz
  · intro hz
    exact L.toPoint_of_mem L.discriminant_ne_zero hz

p2m_export "PeriodPair" "kw_ker_toPointHom"
end PeriodPair
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

namespace ModularCurve

section AtomU4

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
  (K : Type*) [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]

end AtomU4
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

section Reduction

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
  (K : Type*) [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]

end Reduction
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"
end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

section
section

noncomputable section

p2m_open_scoped "PeriodPair P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

namespace PeriodPair
p2m_export "PeriodPair" "lattice ω₁ mk latticeEquivProd g₃ derivWeierstrassP_sq ω₂ G g₂ weierstrassCurve weierstrassCurve_Δ weierstrassCurve_c₄ equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero IsUniformization jLattice JSurjective ofTau scale_indep scale sublatticeIndex discriminant_ne_zero isUniformization_toPoint"
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

theorem scale_lattice : (L.scale α).lattice = Submodule.map (mulLeftZ (α : ℂ)) L.lattice := by
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

private theorem _root_.PeriodPair.mem_scale_lattice_iff {z : ℂ} :
    z ∈ (L.scale α).lattice ↔ ∃ l ∈ L.lattice, z = (α : ℂ) * l := by
  rw [scale_lattice, Submodule.mem_map]; simp only [mulLeftZ_apply]; tauto

p2m_export "PeriodPair" "mem_scale_lattice_iff"
end Scale
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

section Homogeneity

variable (α : ℂˣ)

end Homogeneity
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

section LatticeDependence

variable {L L' : PeriodPair}

end LatticeDependence
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

section Gates

theorem gate_scale_mul (α β : ℂˣ) :
    ((L.scale α).scale β).lattice = (L.scale (β * α)).lattice := by
  ext z
  simp only [mem_scale_lattice_iff, Units.val_mul]
  constructor
  · rintro ⟨-, ⟨l, hl, rfl⟩, rfl⟩; exact ⟨l, hl, (mul_assoc _ _ _).symm⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨(α : ℂ) * l, ⟨l, hl, rfl⟩, mul_assoc _ _ _⟩

end Gates
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve"

end PeriodPair
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"
end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

section
section

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "Module P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.Module"

theorem kw_zlatticeQuotientTorsionCountBridge_axiomAnchor : True :=
  have _h₁ : True = True := propext Iff.rfl
  have _h₂ : ℕ := Classical.choice ⟨0⟩
  have _h₃ : Quot.mk (fun (_ _ : ℕ) => True) 0 = Quot.mk (fun (_ _ : ℕ) => True) 1 :=
    Quot.sound trivial
  trivial

namespace ModularCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

scoped instance (priority := low) kwRealModuleDivisibleByInt : DivisibleBy E ℤ where
  div v n := ((n : ℝ)⁻¹) • v
  div_zero v := by simp
  div_cancel {n} v hn := by
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
    calc n • ((n : ℝ)⁻¹ • v) = (n : ℝ) • ((n : ℝ)⁻¹ • v) := (Int.cast_smul_eq_zsmul ℝ n _).symm
      _ = v := by rw [smul_smul, mul_inv_cancel₀ hn', one_smul]

scoped instance (priority := low) kwRealModuleNoZeroSMulDivisorsInt : NoZeroSMulDivisors ℤ E where
  eq_zero_or_eq_zero_of_smul_eq_zero {n} {v} h := by
    rcases eq_or_ne n 0 with rfl | hn
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h' : (n : ℝ) • v = 0 := by rwa [Int.cast_smul_eq_zsmul ℝ]
      have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
      exact (smul_eq_zero.mp h').resolve_left hn'

variable [FiniteDimensional ℝ E] [ProperSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

def kwLatticeCoeAddEquiv : L ≃+ L.toAddSubgroup where
  toFun x := ⟨(x : E), x.2⟩
  invFun x := ⟨(x : E), x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

scoped instance kwLatticeToAddSubgroupFree : Module.Free ℤ (L.toAddSubgroup) :=
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  Module.Free.of_equiv (kwLatticeCoeAddEquiv L).toIntLinearEquiv

scoped instance kwLatticeToAddSubgroupFinite : Module.Finite ℤ (L.toAddSubgroup) :=
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  Module.Finite.equiv (kwLatticeCoeAddEquiv L).toIntLinearEquiv

theorem kw_card_torsionBy_zlatticeQuotient {n : ℕ} (hn : (n : ℤ) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (E ⧸ L.toAddSubgroup) (n : ℤ)) =
      n ^ Module.finrank ℤ L := by
  have _ := kw_zlatticeQuotientTorsionCountBridge_axiomAnchor
  have h := ModularCurve.card_torsionBy_latticeQuotient (V := E) (L.toAddSubgroup) hn
  rw [h]
  exact congrArg (fun k => n ^ k)
    (LinearEquiv.finrank_eq (kwLatticeCoeAddEquiv L).toIntLinearEquiv).symm

theorem kw_card_torsionBy_zlatticeQuotient_finrank_real
    {n : ℕ} (hn : (n : ℤ) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (E ⧸ L.toAddSubgroup) (n : ℤ)) =
      n ^ Module.finrank ℝ E := by
  rw [kw_card_torsionBy_zlatticeQuotient L hn, ZLattice.rank ℝ L]

end ModularCurve
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

section SatGate

open ModularCurve

end SatGate
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

section
section

noncomputable section

p2m_open_scoped "PeriodPair P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair UpperHalfPlane P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.UpperHalfPlane"
p2m_open "PeriodPair P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair Polynomial P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.Polynomial"

namespace ModularCurve

theorem kw_scale_lattice_toAddSubgroup (L : PeriodPair) (α : ℂˣ) :
    (L.scale α).lattice.toAddSubgroup
      = L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft (α : ℂ)) := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, mem_scale_lattice_iff, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft]
  exact ⟨fun ⟨l, hl, hz⟩ => ⟨l, hl, hz.symm⟩, fun ⟨l, hl, hz⟩ => ⟨l, hl, hz.symm⟩⟩

theorem kwSublatticeIndex_scale (L L' : PeriodPair) (α : ℂˣ) :
    PeriodPair.sublatticeIndex (L.scale α) (L'.scale α) = PeriodPair.sublatticeIndex L L' := by
  have hinj : Function.Injective (AddMonoidHom.mulLeft (α : ℂ)) :=
    fun _ _ h => mul_left_cancel₀ α.ne_zero h
  change AddSubgroup.relIndex _ _ = AddSubgroup.relIndex _ _
  rw [kw_scale_lattice_toAddSubgroup, kw_scale_lattice_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

end ModularCurve
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"
end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve WeierstrassCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.WeierstrassCurve.Affine Polynomial P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.Polynomial P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.AlgebraicCurve PeriodPair P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

namespace ModularCurve

universe u

attribute [local instance] Classical.propDecidable

section HoloLiftMint

end HoloLiftMint
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

section IndexDualMint

def KwD5BetweenCurvesIndexDual : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    (α : ℂˣ)
    (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point),
    (∀ z, L'.kw_toPointHom ((α : ℂ) * z) = ψ (L.kw_toPointHom z)) →
    ∃ (β : ℂˣ), ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = Nat.card ψ.ker

end IndexDualMint
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

section Reduce

end Reduce
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

section UpdatedWires

end UpdatedWires
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end ModularCurve
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve PeriodPair P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

namespace ModularCurve

theorem kw_surgehgf4_hID_axiomAnchor : True := by
  have _p : (True ∨ True) = True := propext (by tauto)
  have _c := Classical.em True
  have _q := Quot.sound (r := fun _ _ : Unit => True) (a := ()) (b := ()) trivial
  trivial

section BetweenCurves

variable (L L' : PeriodPair)
  [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
  (α : ℂˣ)
  (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
  (hint : ∀ z, L'.kw_toPointHom ((α : ℂ) * z) = ψ (L.kw_toPointHom z))

include hint in

def kw_surgehgf4_hID_kerIndexHom : L'.lattice.toAddSubgroup →+ ψ.ker where
  toFun l' := ⟨L.kw_toPointHom ((α : ℂ)⁻¹ * (l' : ℂ)), by
    rw [AddMonoidHom.mem_ker, ← hint ((α : ℂ)⁻¹ * (l' : ℂ)),
      mul_inv_cancel_left₀ α.ne_zero]
    have hl'0 : L'.kw_toPointHom (l' : ℂ) = 0 := by
      rw [← AddMonoidHom.mem_ker, L'.kw_ker_toPointHom]; exact l'.2
    exact hl'0⟩
  map_zero' := Subtype.ext <| by simp
  map_add' l'₁ l'₂ := Subtype.ext <| by
    push_cast; rw [mul_add]; exact map_add L.kw_toPointHom _ _

include hint in
theorem kw_surgehgf4_hID_kerIndexHom_apply (l' : L'.lattice.toAddSubgroup) :
    (kw_surgehgf4_hID_kerIndexHom L L' α ψ hint l' : L.weierstrassCurve.toAffine.Point)
      = L.kw_toPointHom ((α : ℂ)⁻¹ * (l' : ℂ)) := rfl

include hint in

theorem kw_surgehgf4_hID_scale_subset :
    ((L.scale α).lattice : Set ℂ) ⊆ L'.lattice := by
  intro z hz
  rw [SetLike.mem_coe, L.mem_scale_lattice_iff] at hz
  obtain ⟨l, hl, rfl⟩ := hz
  rw [SetLike.mem_coe, ← Submodule.mem_toAddSubgroup, ← L'.kw_ker_toPointHom,
    AddMonoidHom.mem_ker, hint]
  have hl0 : L.kw_toPointHom l = 0 := by
    rw [← AddMonoidHom.mem_ker, L.kw_ker_toPointHom]; exact hl
  rw [hl0, _root_.map_zero]

include hint in

theorem kw_surgehgf4_hID_kerIndexHom_surjective :
    Function.Surjective (kw_surgehgf4_hID_kerIndexHom L L' α ψ hint) := by
  rintro ⟨P, hP⟩
  obtain ⟨z, hz⟩ := (L.kw_isUniformization).2.1 P
  have hαz : (α : ℂ) * z ∈ L'.lattice.toAddSubgroup := by
    rw [← L'.kw_ker_toPointHom, AddMonoidHom.mem_ker, hint, L.kw_toPointHom_apply, hz]
    exact hP
  exact ⟨⟨(α : ℂ) * z, hαz⟩, Subtype.ext <| by
    simp only [kw_surgehgf4_hID_kerIndexHom_apply, inv_mul_cancel_left₀ α.ne_zero,
      L.kw_toPointHom_apply, hz]⟩

include hint in

theorem kw_surgehgf4_hID_ker_kerIndexHom :
    (kw_surgehgf4_hID_kerIndexHom L L' α ψ hint).ker
      = (L.scale α).lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup := by
  ext ⟨l', hl'⟩
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    rw [Submodule.mem_toAddSubgroup, L.mem_scale_lattice_iff]
    refine ⟨(α : ℂ)⁻¹ * l', ?_, (mul_inv_cancel_left₀ α.ne_zero l').symm⟩
    have h0 : L.kw_toPointHom ((α : ℂ)⁻¹ * l') = 0 := Subtype.ext_iff.mp h
    rwa [← AddMonoidHom.mem_ker, L.kw_ker_toPointHom, Submodule.mem_toAddSubgroup] at h0
  · intro h
    rw [Submodule.mem_toAddSubgroup, L.mem_scale_lattice_iff] at h
    obtain ⟨v, hv, hvl'⟩ := h
    apply Subtype.ext
    show L.kw_toPointHom ((α : ℂ)⁻¹ * l') = 0
    rw [show (l' : ℂ) = (α : ℂ) * v from hvl', inv_mul_cancel_left₀ α.ne_zero,
      ← AddMonoidHom.mem_ker, L.kw_ker_toPointHom]
    exact hv

include hint in

theorem kw_surgehgf4_hID_forwardIndex_eq_card_ker :
    PeriodPair.sublatticeIndex L' (L.scale α) = Nat.card ψ.ker := by
  unfold PeriodPair.sublatticeIndex
  rw [← kw_surgehgf4_hID_ker_kerIndexHom L L' α ψ hint, ← Nat.card_congr
    (QuotientAddGroup.liftEquiv _
      (kw_surgehgf4_hID_kerIndexHom_surjective L L' α ψ hint) rfl).toEquiv]
  rfl

include hint in

theorem kw_surgehgf4_hID_card_smul_subset :
    ∀ l' ∈ L'.lattice, (Nat.card ψ.ker : ℂ) * l' ∈ (L.scale α).lattice := by
  intro l' hl'
  set N := Nat.card ψ.ker with hNdef
  have hidx : ((L.scale α).lattice.toAddSubgroup.addSubgroupOf
      L'.lattice.toAddSubgroup).index = N := by
    have h := kw_surgehgf4_hID_forwardIndex_eq_card_ker L L' α ψ hint
    unfold PeriodPair.sublatticeIndex at h; exact h

  set H := (L.scale α).lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup with hHdef
  have hmem : N • (⟨l', hl'⟩ : L'.lattice.toAddSubgroup) ∈ H := hidx ▸ H.nsmul_index_mem _
  rw [hHdef, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup] at hmem

  have heq : ((N • (⟨l', hl'⟩ : L'.lattice.toAddSubgroup) : L'.lattice.toAddSubgroup) : ℂ)
      = (Nat.card ψ.ker : ℂ) * l' := by
    rw [AddSubmonoidClass.coe_nsmul, nsmul_eq_mul, hNdef]
  rw [← heq]; exact hmem

end BetweenCurves
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

noncomputable def kw_surgehgf4_hID_dualUnit {X Y : Type*} [AddGroup X] [AddGroup Y]
    (α : ℂˣ) (ψ : X →+ Y) (hN : 0 < Nat.card ψ.ker) : ℂˣ :=
  Units.mk0 (Nat.card ψ.ker : ℂ) (by exact_mod_cast hN.ne') * α⁻¹

theorem kw_surgehgf4_hID_dualUnit_val {X Y : Type*} [AddGroup X] [AddGroup Y]
    (α : ℂˣ) (ψ : X →+ Y) (hN : 0 < Nat.card ψ.ker) :
    (kw_surgehgf4_hID_dualUnit α ψ hN : ℂ) = (Nat.card ψ.ker : ℂ) * (α : ℂ)⁻¹ := by
  simp only [kw_surgehgf4_hID_dualUnit, Units.val_mul, Units.val_mk0,
    Units.val_inv_eq_inv_val]

section BetweenCurves

variable (L L' : PeriodPair)
  [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
  (α : ℂˣ)
  (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
  (hint : ∀ z, L'.kw_toPointHom ((α : ℂ) * z) = ψ (L.kw_toPointHom z))

include hint in

theorem kw_surgehgf4_hID_dual_subset (hN : 0 < Nat.card ψ.ker) :
    ((L'.scale (kw_surgehgf4_hID_dualUnit α ψ hN)).lattice : Set ℂ) ⊆ L.lattice := by
  intro z hz
  rw [SetLike.mem_coe, L'.mem_scale_lattice_iff] at hz
  obtain ⟨l', hl', rfl⟩ := hz
  have hNl' := kw_surgehgf4_hID_card_smul_subset L L' α ψ hint l' hl'
  rw [L.mem_scale_lattice_iff] at hNl'
  obtain ⟨v, hv, hveq⟩ := hNl'
  rw [SetLike.mem_coe, kw_surgehgf4_hID_dualUnit_val α ψ hN, mul_assoc,
    show (Nat.card ψ.ker : ℂ) * ((α : ℂ)⁻¹ * l')
      = (α : ℂ)⁻¹ * ((Nat.card ψ.ker : ℂ) * l') from by ring,
    hveq, inv_mul_cancel_left₀ α.ne_zero]
  exact hv

theorem kw_surgehgf4_hID_sublatticeIndex_congr_snd {A M M' : PeriodPair}
    (h : M.lattice = M'.lattice) :
    PeriodPair.sublatticeIndex A M = PeriodPair.sublatticeIndex A M' := by
  unfold PeriodPair.sublatticeIndex; rw [h]

def kw_surgehgf4_hID_scaleIndexHom (M : PeriodPair) {N : ℕ} (hN : 0 < N) :
    M.lattice.toAddSubgroup
      →+ (Submodule.torsionBy ℤ (ℂ ⧸ M.lattice.toAddSubgroup) (N : ℤ)) where
  toFun l := ⟨QuotientAddGroup.mk ((N : ℂ)⁻¹ * (l : ℂ)), by
    rw [Submodule.mem_torsionBy_iff, ← QuotientAddGroup.mk_zsmul,
      QuotientAddGroup.eq_zero_iff]

    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (N : ℤ) • ((N : ℂ)⁻¹ * (l : ℂ)) = (l : ℂ) := by
      rw [zsmul_eq_mul, Int.cast_natCast, mul_inv_cancel_left₀ hNne]
    rw [this]; exact l.2⟩
  map_zero' := Subtype.ext <| by simp
  map_add' l₁ l₂ := Subtype.ext <| by

    simp only [AddSubgroup.coe_add, mul_add]
    rfl

theorem kw_surgehgf4_hID_sublatticeIndex_scale_nat (M : PeriodPair)
    {N : ℕ} (hN : 0 < N) :
    PeriodPair.sublatticeIndex M (M.scale (Units.mk0 (N : ℂ) (by exact_mod_cast hN.ne'))) = N ^ 2 := by
  set Nu := Units.mk0 (N : ℂ) (by exact_mod_cast hN.ne') with hNudef
  have hNuval : (Nu : ℂ) = (N : ℂ) := by rw [hNudef, Units.val_mk0]
  have hNinv : (Nu : ℂ)⁻¹ = (N : ℂ)⁻¹ := by rw [hNuval]

  have hsurj : Function.Surjective (kw_surgehgf4_hID_scaleIndexHom M hN) := by
    rintro ⟨x, hx⟩
    rw [Submodule.mem_torsionBy_iff] at hx
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hNz : (N : ℂ) * z ∈ M.lattice.toAddSubgroup := by
      have : (N : ℤ) • z ∈ M.lattice.toAddSubgroup := by
        rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_zsmul]; exact hx
      simpa [zsmul_eq_mul] using this
    refine ⟨⟨(N : ℂ) * z, hNz⟩, Subtype.ext ?_⟩
    show QuotientAddGroup.mk ((N : ℂ)⁻¹ * ((N : ℂ) * z)) = QuotientAddGroup.mk z
    rw [inv_mul_cancel_left₀ (by exact_mod_cast hN.ne' : (N : ℂ) ≠ 0)]

  have hker : (kw_surgehgf4_hID_scaleIndexHom M hN).ker
      = (M.scale Nu).lattice.toAddSubgroup.addSubgroupOf M.lattice.toAddSubgroup := by
    ext ⟨l, hl⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      M.mem_scale_lattice_iff]
    constructor
    · intro h0
      have h0' : (N : ℂ)⁻¹ * l ∈ M.lattice.toAddSubgroup := by
        have := Subtype.ext_iff.mp h0
        simp only [kw_surgehgf4_hID_scaleIndexHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          ZeroMemClass.coe_zero] at this
        rwa [QuotientAddGroup.eq_zero_iff] at this
      exact ⟨(N : ℂ)⁻¹ * l, h0',
        by rw [hNuval, mul_inv_cancel_left₀ (by exact_mod_cast hN.ne' : (N : ℂ) ≠ 0)]⟩
    · rintro ⟨v, hv, hvl⟩
      apply Subtype.ext
      show QuotientAddGroup.mk ((N : ℂ)⁻¹ * l) = 0
      rw [QuotientAddGroup.eq_zero_iff,
        show l = (N : ℂ) * v from hNuval ▸ hvl,
        inv_mul_cancel_left₀ (by exact_mod_cast hN.ne' : (N : ℂ) ≠ 0)]
      exact hv

  have htor : Nat.card ↥(Submodule.torsionBy ℤ (ℂ ⧸ M.lattice.toAddSubgroup) (N : ℤ))
      = N ^ 2 := by
    rw [kw_card_torsionBy_zlatticeQuotient_finrank_real M.lattice
      (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0), Complex.finrank_real_complex]

  unfold PeriodPair.sublatticeIndex
  rw [← hker, ← htor, ← Nat.card_congr
    (QuotientAddGroup.liftEquiv _ hsurj rfl).toEquiv]
  rfl

include hint in

theorem kw_surgehgf4_hID_card_ker_pos : 0 < Nat.card ψ.ker := by
  rw [← kw_surgehgf4_hID_forwardIndex_eq_card_ker L L' α ψ hint]
  refine Nat.pos_of_ne_zero ?_

  have hle : (L.scale α).lattice ≤ L'.lattice :=
    fun z hz => kw_surgehgf4_hID_scale_subset L L' α ψ hint hz

  have hcov := ZLattice.covolume_div_covolume_eq_relIndex'
    (L.scale α).lattice L'.lattice hle
  have hpos₁ : (0 : ℝ) < ZLattice.covolume (L.scale α).lattice :=
    ZLattice.covolume_pos (L.scale α).lattice MeasureTheory.volume
  have hpos₂ : (0 : ℝ) < ZLattice.covolume L'.lattice :=
    ZLattice.covolume_pos L'.lattice MeasureTheory.volume
  have hratio : (0 : ℝ) < ZLattice.covolume (L.scale α).lattice
      / ZLattice.covolume L'.lattice := div_pos hpos₁ hpos₂

  intro h0
  unfold PeriodPair.sublatticeIndex at h0

  have h0R : ((L.scale α).lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup : ℝ)
      = 0 := by exact_mod_cast h0
  rw [← hcov] at h0R
  exact absurd h0R (ne_of_gt hratio)

include hint in

theorem kw_surgehgf4_hID_dualIndex_eq (hN : 0 < Nat.card ψ.ker) :
    PeriodPair.sublatticeIndex L (L'.scale (kw_surgehgf4_hID_dualUnit α ψ hN))
      = Nat.card ψ.ker := by
  set N := Nat.card ψ.ker with hNdef
  set β := kw_surgehgf4_hID_dualUnit α ψ hN with hβdef
  set Nu := Units.mk0 (N : ℂ) (by exact_mod_cast hN.ne') with hNudef

  have h1 : PeriodPair.sublatticeIndex L (L'.scale β)
      = PeriodPair.sublatticeIndex (L.scale α) ((L'.scale β).scale α) :=
    (kwSublatticeIndex_scale L (L'.scale β) α).symm

  have hαβ : α * β = Nu := by
    apply Units.ext
    simp only [hβdef, hNudef, Units.val_mul, kw_surgehgf4_hID_dualUnit_val,
      Units.val_mk0]
    field_simp
    exact_mod_cast hNdef.symm
  have h2 : ((L'.scale β).scale α).lattice = (L'.scale Nu).lattice := by
    rw [gate_scale_mul L' β α, hαβ]

  have h3 : PeriodPair.sublatticeIndex (L.scale α) ((L'.scale β).scale α)
      = PeriodPair.sublatticeIndex (L.scale α) (L'.scale Nu) :=
    kw_surgehgf4_hID_sublatticeIndex_congr_snd h2
  rw [h1, h3]

  have hsub1 : ((L'.scale Nu).lattice : Set ℂ) ⊆ (L.scale α).lattice := by
    intro z hz
    rw [SetLike.mem_coe, L'.mem_scale_lattice_iff] at hz
    obtain ⟨l', hl', rfl⟩ := hz
    simp only [hNudef, Units.val_mk0]
    exact kw_surgehgf4_hID_card_smul_subset L L' α ψ hint l' hl'
  have hsub2 : ((L.scale α).lattice : Set ℂ) ⊆ L'.lattice :=
    kw_surgehgf4_hID_scale_subset L L' α ψ hint
  have htower : PeriodPair.sublatticeIndex L' (L'.scale Nu)
      = PeriodPair.sublatticeIndex (L.scale α) (L'.scale Nu)
        * PeriodPair.sublatticeIndex L' (L.scale α) := by
    unfold PeriodPair.sublatticeIndex

    have hle1 : (L'.scale Nu).lattice.toAddSubgroup ≤ (L.scale α).lattice.toAddSubgroup := by
      intro z hz; exact hsub1 hz
    have hle2 : (L.scale α).lattice.toAddSubgroup ≤ L'.lattice.toAddSubgroup := by
      intro z hz; exact hsub2 hz
    exact (AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2).symm

  have hN2 : PeriodPair.sublatticeIndex L' (L'.scale Nu) = N ^ 2 :=
    kw_surgehgf4_hID_sublatticeIndex_scale_nat L' hN
  have hfwd : PeriodPair.sublatticeIndex L' (L.scale α) = N :=
    kw_surgehgf4_hID_forwardIndex_eq_card_ker L L' α ψ hint

  rw [hN2, hfwd] at htower
  have : PeriodPair.sublatticeIndex (L.scale α) (L'.scale Nu) * N = N * N := by
    rw [← htower]; ring
  exact Nat.eq_of_mul_eq_mul_right hN this

theorem kw_surgehgf4_hID_betweenCurvesIndexDual_proved :
    KwD5BetweenCurvesIndexDual := by
  have _ := kw_surgehgf4_hID_axiomAnchor
  intro L L' _ _ α ψ hint
  have hN := kw_surgehgf4_hID_card_ker_pos L L' α ψ hint
  exact ⟨kw_surgehgf4_hID_dualUnit α ψ hN,
    kw_surgehgf4_hID_dual_subset L L' α ψ hint hN,
    kw_surgehgf4_hID_dualIndex_eq L L' α ψ hint hN⟩

end BetweenCurves
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end ModularCurve
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

end
p2m_reactivate "P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.ModularCurve P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.PeriodPair"

theorem solution (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) (α : ℂˣ)
    (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
    (hψ : ∀ z : ℂ, L'.toPoint hL' ((α : ℂ) * z) = ψ (L.toPoint hL z)) :
    ∃ β : ℂˣ, ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = Nat.card ψ.ker := by
  haveI : L.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr L.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩
  haveI : L'.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr L'.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩
  refine ModularCurve.kw_surgehgf4_hID_betweenCurvesIndexDual_proved L L' α ψ ?_
  intro z
  rw [PeriodPair.kw_toPointHom_apply, PeriodPair.kw_toPointHom_apply]
  exact hψ z

end S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker
end P2MW
export P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker (solution)
