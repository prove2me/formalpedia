-- Prove2me | solution 1 for PDivisibleGroup.Tower.eq_of_frobenius_comp_eq_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6af62f81-c42d-535d-b70e-613873a8fe62

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_Tower_nsmulAlgHom_apply_eq_zero_iff_transition_apply_eq_zero_zmodp
import Theorems.Thm_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Tower_eq_of_frobenius_comp_eq_zmodp
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe v

theorem solution
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (A : ℕ → Type v) [∀ v, CommRing (A v)] [∀ v, HopfAlgebra (ZMod p) (A v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (A v)] [∀ v, Module.Finite (ZMod p) (A v)]
    (t : ∀ v, A (v + 1) →ₐc[ZMod p] A v) (ht : ∀ v, Function.Surjective (t v))
    (hrank : ∀ v, Module.finrank (ZMod p) (A v) = p ^ (v * h))
    (hker : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (A (v + 1)) (p ^ v))
    (e e' : ∀ v : ℕ, A v →ₐ[ZMod p] A v)
    (het : ∀ v, (t v : A (v + 1) →ₐ[ZMod p] A v).comp (e (v + 1)) = (e v).comp (t v : A (v + 1) →ₐ[ZMod p] A v))
    (he't : ∀ v, (t v : A (v + 1) →ₐ[ZMod p] A v).comp (e' (v + 1)) = (e' v).comp (t v : A (v + 1) →ₐ[ZMod p] A v))
    (hF : ∀ (v : ℕ) (a : A (v + 1)), (e (v + 1) a) ^ p = (e' (v + 1) a) ^ p) :
    ∀ v : ℕ, e v = e' v := by
  intro v
  obtain ⟨V, -, hV, -⟩ := PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp p (A (v + 1))

  have key : ∀ a : A (v + 1), t v (e (v + 1) a) = t v (e' (v + 1) a) := by
    intro a
    rw [← sub_eq_zero, ← map_sub,
      ← PDivisibleGroup.Tower.nsmulAlgHom_apply_eq_zero_iff_transition_apply_eq_zero_zmodp p h A t ht hrank hker v,
      map_sub, ← hV, ← hV, hF, sub_self]
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := ht v x
  have h1 := AlgHom.congr_fun (het v) a
  have h2 := AlgHom.congr_fun (he't v) a
  simp only [AlgHom.comp_apply] at h1 h2
  rw [show (t v : A (v + 1) →ₐ[ZMod p] A v) a = t v a from rfl] at h1 h2
  rw [← h1, ← h2]
  exact key a

end S_PDivisibleGroup_Tower_eq_of_frobenius_comp_eq_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_Tower_eq_of_frobenius_comp_eq_zmodp (solution)
