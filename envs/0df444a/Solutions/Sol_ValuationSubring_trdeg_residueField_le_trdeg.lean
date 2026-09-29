-- Prove2me | solution 1 for ValuationSubring.trdeg_residueField_le_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bd890ac2-b14c-5f58-ab07-6502734b8881

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg

set_option autoImplicit false

open Cardinal

namespace ValuationSubring
p2m_export "ValuationSubring" "comap mem_comap toSubring ext valuation_le_one_iff algebra valuation inclusion"
namespace ResidueTrdeg
p2m_open "ValuationSubring"

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

abbrev B : ValuationSubring K := A.comap (algebraMap K L)

def resHom : B K A →+* A :=
  (algebraMap K L).restrict (B K A).toSubring A.toSubring (fun _ hx => hx)

@[scoped simp] lemma coe_resHom_apply (b : B K A) : ((resHom K A b : A) : L) = algebraMap K L (b : K) := rfl

lemma algebraMap_comp_resHom :
    (algebraMap A L).comp (resHom K A) = (algebraMap K L).comp (algebraMap (B K A) K) := by
  ext b
  rfl

theorem algebraicIndependent_lift
    [Algebra (IsLocalRing.ResidueField (B K A)) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : B K A,
      algebraMap (IsLocalRing.ResidueField (B K A)) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩)
    {ι : Type*} (y : ι → A)
    (hind : AlgebraicIndependent (IsLocalRing.ResidueField (B K A))
      (fun i => IsLocalRing.residue A (y i))) :
    AlgebraicIndependent K (fun i => ((y i : A) : L)) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0

  have hsupp : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hP0
  obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image P.support
    (fun m => A.valuation (algebraMap K L (P.coeff m))) hsupp
  set c : K := P.coeff m₀ with hc
  have hc0 : c ≠ 0 := MvPolynomial.mem_support_iff.mp hm₀

  set Q : MvPolynomial ι K := MvPolynomial.C c⁻¹ * P with hQ
  have hQcoeff : ∀ m, Q.coeff m = c⁻¹ * P.coeff m := fun m => by
    rw [hQ, MvPolynomial.coeff_C_mul]
  have hQm₀ : Q.coeff m₀ = 1 := by rw [hQcoeff, ← hc, inv_mul_cancel₀ hc0]
  have hQeval : MvPolynomial.aeval (fun i => ((y i : A) : L)) Q = 0 := by
    rw [hQ, map_mul, hP, mul_zero]

  have hQmem : ∀ m, algebraMap K L (Q.coeff m) ∈ A := by
    intro m
    rw [← A.valuation_le_one_iff, hQcoeff, map_mul, map_mul, map_inv₀, map_inv₀]
    by_cases hm : m ∈ P.support
    · have hle := hmax m hm
      have hcv : A.valuation (algebraMap K L c) ≠ 0 := by
        rw [Ne, Valuation.zero_iff, map_eq_zero]
        exact hc0
      calc (A.valuation (algebraMap K L c))⁻¹ * A.valuation (algebraMap K L (P.coeff m))
          ≤ (A.valuation (algebraMap K L c))⁻¹ * A.valuation (algebraMap K L c) := by
            gcongr
        _ = 1 := inv_mul_cancel₀ hcv
    · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero, map_zero, mul_zero]
      exact zero_le_one

  obtain ⟨QB, hQB⟩ : Q ∈ Set.range (MvPolynomial.map (algebraMap (B K A) K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro d hd
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hd
    exact ⟨⟨Q.coeff m, hQmem m⟩, rfl⟩

  have heval : MvPolynomial.eval₂ (resHom K A) y QB = 0 := by
    have h : algebraMap A L (MvPolynomial.eval₂ (resHom K A) y QB) = 0 := by
      rw [MvPolynomial.eval₂_comp_left, algebraMap_comp_resHom, ← MvPolynomial.eval₂_map, hQB]
      exact hQeval
    apply Subtype.val_injective
    show algebraMap A L (MvPolynomial.eval₂ (resHom K A) y QB) = algebraMap A L 0
    rw [h, map_zero]

  have hres : MvPolynomial.aeval (fun i => IsLocalRing.residue A (y i))
      (MvPolynomial.map (IsLocalRing.residue (B K A)) QB) = 0 := by
    have h1 := congrArg (IsLocalRing.residue A) heval
    rw [map_zero, MvPolynomial.eval₂_comp_left] at h1
    have h2 : (IsLocalRing.residue A).comp (resHom K A) =
        (algebraMap (IsLocalRing.ResidueField (B K A)) (IsLocalRing.ResidueField A)).comp
          (IsLocalRing.residue (B K A)) := by
      ext b
      simp only [RingHom.comp_apply]
      rw [hcompat b]
      rfl
    rw [h2, ← MvPolynomial.eval₂_map] at h1
    rw [MvPolynomial.aeval_def]
    exact h1
  have hzero : MvPolynomial.map (IsLocalRing.residue (B K A)) QB = 0 :=
    (algebraicIndependent_iff.mp hind) _ hres

  have h1 : QB.coeff m₀ = 1 := by
    have h : algebraMap (B K A) K (QB.coeff m₀) = algebraMap (B K A) K 1 := by
      rw [← MvPolynomial.coeff_map, hQB, hQm₀, map_one]
    exact Subtype.val_injective h
  have h2 := congrArg (MvPolynomial.coeff m₀) hzero
  rw [MvPolynomial.coeff_map, h1, map_one, MvPolynomial.coeff_zero] at h2
  exact one_ne_zero h2

theorem main
    [Algebra (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : A.comap (algebraMap K L),
      algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩) :
    Algebra.trdeg (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
        (IsLocalRing.ResidueField A) ≤ Algebra.trdeg K L := by
  classical
  rw [Algebra.trdeg]
  refine ciSup_le' fun s => ?_

  choose y hy using fun i : s.1 => IsLocalRing.residue_surjective (R := A) (i : IsLocalRing.ResidueField A)
  have hind : AlgebraicIndependent (IsLocalRing.ResidueField (B K A))
      (fun i : s.1 => IsLocalRing.residue A (y i)) := by
    have : (fun i : s.1 => IsLocalRing.residue A (y i)) = fun i : s.1 => (i : IsLocalRing.ResidueField A) :=
      funext hy
    rw [this]
    exact s.2
  have hK := algebraicIndependent_lift K A hcompat y hind
  exact hK.cardinalMk_le_trdeg

end ValuationSubring.ResidueTrdeg
p2m_reactivate "P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg.ValuationSubring P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg.ValuationSubring.ResidueTrdeg"
p2m_reactivate "P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg.ValuationSubring"

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Algebra (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : A.comap (algebraMap K L),
      algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩) :
    Algebra.trdeg (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
        (IsLocalRing.ResidueField A) ≤ Algebra.trdeg K L :=
  ValuationSubring.ResidueTrdeg.main K A hcompat

end S_ValuationSubring_trdeg_residueField_le_trdeg
end P2MW
export P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg (solution)
