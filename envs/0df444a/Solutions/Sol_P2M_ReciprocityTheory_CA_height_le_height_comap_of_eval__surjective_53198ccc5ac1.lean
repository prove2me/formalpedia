-- Prove2me | solution 1 for P2M_ReciprocityTheory_CA_height_le_height_comap_of_eval__surjective_53198ccc5ac1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:14:21.57523+00:00
-- url     : https://prove2.me/submissions/68093cc8-8c9f-455b-a3aa-cb89ea45d94b

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
import Theorems.Thm_ReciprocityTheory_CA_height_le_height_comap_C_add_one
import Theorems.Thm_ReciprocityTheory_CA_height_add_one_le_height_comap_of_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open Polynomial
namespace ReciprocityTheory.CA
theorem _root_.solution {R S : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) (x : S)
    (hgen : Function.Surjective (eval₂RingHom f x)) (halg : ∃ g : R[X], g ≠ 0 ∧ eval₂ f x g = 0)
    (q : Ideal S) [q.IsPrime] : q.height ≤ (q.comap f).height := by
  have hker : RingHom.ker (eval₂RingHom f x) ≠ ⊥ := by
    obtain ⟨g, hg0, hg⟩ := halg
    intro h
    apply hg0
    have hmem : g ∈ RingHom.ker (eval₂RingHom f x) := by
      rw [RingHom.mem_ker]
      simpa using hg
    rw [h, Ideal.mem_bot] at hmem
    exact hmem
  have h3 := height_add_one_le_height_comap_of_surjective (eval₂RingHom f x) hgen hker q
  have h2 := height_le_height_comap_C_add_one (q.comap (eval₂RingHom f x))
  have hc : (q.comap (eval₂RingHom f x)).comap (C : R →+* R[X]) = q.comap f := by
    rw [Ideal.comap_comap]
    congr 1
    ext r
    simp
  rw [hc] at h2
  exact (WithTop.add_le_add_iff_right ENat.one_ne_top).mp (h3.trans h2)
end ReciprocityTheory.CA
