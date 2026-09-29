-- Prove2me | solution 1 for ValuationSubring.exists_algebraicIndependent_residue_of_le_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e4b8ac2f-12cc-59bd-9603-20e69507ed83

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg

set_option autoImplicit false

universe u v

theorem solution
    {k : Type u} {K : Type v} [Field k] [Field K] (c : k →+* K) (O : ValuationSubring K)
    (hc : ∀ x : k, c x ∈ O) {d : ℕ}
    (hd :
      letI : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      (d : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField O)) :
    ∃ (g : Fin d → K) (hg : ∀ i, g i ∈ O),
      letI : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩) := by
  classical
  letI instAlg : Algebra k (IsLocalRing.ResidueField O) :=
    ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra

  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' k (IsLocalRing.ResidueField O)
  have hcard : (d : Cardinal) ≤ Cardinal.mk ι := by rw [hx.cardinalMk_eq_trdeg]; exact hd

  have hemb : Nonempty (Fin d ↪ ι) := by
    rw [← Cardinal.lift_mk_le']
    simpa using hcard
  obtain ⟨e⟩ := hemb
  have hind : AlgebraicIndependent k (x ∘ e) := hx.1.comp e e.injective

  have hl : ∀ i, ∃ y : ↥O, IsLocalRing.residue ↥O y = x (e i) := fun i => IsLocalRing.residue_surjective _
  choose gO hgO using hl
  refine ⟨fun i => (gO i : K), fun i => (gO i).2, ?_⟩
  have : (fun i => IsLocalRing.residue ↥O ⟨(gO i : K), (gO i).2⟩) = x ∘ e := funext fun i => hgO i
  rw [this]
  exact hind

end S_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg
end P2MW
export P2MW.S_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg (solution)
