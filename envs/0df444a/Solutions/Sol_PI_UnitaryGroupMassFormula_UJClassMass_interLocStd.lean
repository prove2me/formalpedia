-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.interLocStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:45.117204+00:00
-- url     : https://prove2.me/submissions/b7bf1747-6e1d-46d2-be2e-92da8c593fbb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Theorems.Thm_latLocGlob


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
  [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution [FiniteDimensional E V] (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (x : V)
    (hx : ∀ p : Ideal (𝓞 E), p.IsMaximal → ∃ t : 𝓞 E, t ∉ p ∧ t • x ∈ N) : x ∈ N := by
  classical
  have hfull : PI.LatLocGlob.IsFullLat E N := ⟨hN.fg, hN.span_eq_top⟩
  let N' : Submodule (𝓞 E) V := N ⊔ Submodule.span (𝓞 E) {x}
  have hfull' : PI.LatLocGlob.IsFullLat E N' := by
    refine ⟨hN.fg.sup (Submodule.fg_span_singleton x), ?_⟩
    apply eq_top_iff.2
    rw [← hN.span_eq_top]
    exact Submodule.span_mono (fun y hy => Submodule.mem_sup_left hy)
  have hloc : ∀ p : Ideal (𝓞 E), p.IsMaximal → PI.LatLocGlob.loc p N' = PI.LatLocGlob.loc p N := by
    intro p hp
    haveI := hp.isPrime
    ext y
    constructor
    · rintro ⟨s, hs, hsy⟩
      obtain ⟨a, ha, z, hz, haz⟩ := Submodule.mem_sup.1 hsy
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
      obtain ⟨t, ht, htx⟩ := hx p hp
      refine ⟨t * s, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht hs, ?_⟩
      rw [mul_smul, ← haz, smul_add, smul_comm t r x]
      exact N.add_mem (N.smul_mem t ha) (N.smul_mem r htx)
    · rintro ⟨s, hs, hsy⟩
      exact ⟨s, hs, Submodule.mem_sup_left hsy⟩
  obtain ⟨L, _, huniq⟩ := latLocGlob (𝓞 E) E V N hfull (fun p => PI.LatLocGlob.loc p N)
    (fun p _ => ⟨N, hfull, rfl⟩) (Set.finite_empty.subset (fun p hp => hp.2 rfl))
  have e1 : N = L := huniq N ⟨hfull, fun p _ => rfl⟩
  have e2 : N' = L := huniq N' ⟨hfull', hloc⟩
  have : x ∈ N' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  rwa [e2, ← e1] at this
end PI.UnitaryGroupMassFormula.UJClassMass
