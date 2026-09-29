-- Prove2me | solution 1 for ValuationSubring.exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/febf3ebc-52e7-56bb-bb31-fdd967e497bc

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_and_finrank_le_of_forall_finset
import Theorems.Thm_ValuationSubring_finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh] [IsDiscreteValuationRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) (hιP : ∀ t : AlgebraicClosure ℚ, t ∈ Pl ↔ ‖ι t‖ ≤ 1) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] K' ∧ ∀ x : Rh, ι (algebraMap Rh (AlgebraicClosure ℚ) x) ∈ K' := by
  classical

  let S : Set (PadicAlgCl p) := Set.range (fun x : Rh => ι (algebraMap Rh (AlgebraicClosure ℚ) x))
  have hp0 : (p : Rh) ≠ 0 := by
    intro h
    have : (p : AlgebraicClosure ℚ) = 0 := by rw [← map_natCast (algebraMap Rh (AlgebraicClosure ℚ)), h, map_zero]
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  have he : IsDiscreteValuationRing.addVal Rh (p : Rh) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hp0
  obtain ⟨e, he'⟩ := ENat.ne_top_iff_exists.mp he
  have hS : ∀ s : Finset (PadicAlgCl p), (↑s : Set (PadicAlgCl p)) ⊆ S →
      FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] (↑s : Set (PadicAlgCl p))) ∧
        Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] (↑s : Set (PadicAlgCl p))) ≤ e := by
    intro s hs

    have hlift : ∀ y ∈ s, ∃ x : Rh, ι (algebraMap Rh (AlgebraicClosure ℚ) x) = y := fun y hy => hs (Finset.mem_coe.mpr hy)
    choose f hf using hlift
    let t : Finset Rh := s.attach.image (fun y => f y.1 y.2)
    have himg : (fun x : Rh => ι (algebraMap Rh (AlgebraicClosure ℚ) x)) '' (↑t : Set Rh) = (↑s : Set (PadicAlgCl p)) := by
      ext z
      simp only [Set.mem_image, Finset.mem_coe, t, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩; rw [hf y hy]; exact hy
      · intro hz; exact ⟨f z hz, ⟨z, hz, rfl⟩, hf z hz⟩
    obtain ⟨hfin, hle⟩ := ValuationSubring.finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime
      p Pl hPl Rh hRA hRloc hres ι hιP t
    rw [himg] at hfin hle
    refine ⟨hfin, ?_⟩
    rw [← he'] at hle
    exact_mod_cast hle
  obtain ⟨hfinS, -⟩ := IntermediateField.finiteDimensional_adjoin_and_finrank_le_of_forall_finset S e hS
  exact ⟨IntermediateField.adjoin ℚ_[p] S, hfinS, fun x => IntermediateField.subset_adjoin ℚ_[p] S ⟨x, rfl⟩⟩

end S_ValuationSubring_exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime (solution)
