-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.prod_map_pow_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:25.382335+00:00
-- url     : https://prove2.me/submissions/0184cb72-f8f6-41fa-8181-cd59f7707c6f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreBb
theorem _root_.solution {M : Type*} [Monoid M] {ι : Type*} [DecidableEq ι] (P : ι → M)
    (hP : ∀ i j, Commute (P i) (P j)) (e : ι → ℕ) (k : ι) :
    ∀ L : List ι, L.Nodup → k ∈ L →
      (L.map fun i => P i ^ (e i + if i = k then 1 else 0)).prod = (L.map fun i => P i ^ e i).prod * P k
  | [], _, h => absurd h (List.not_mem_nil)
  | a :: L, hL, hk => by
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    have hcomm : ∀ x, Commute (P x) (L.map fun i => P i ^ e i).prod := fun x =>
      Commute.list_prod_right _ _ (fun y hy => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hy
        exact (hP x i).pow_right _)
    by_cases hak : a = k
    · subst hak
      have hrest : (L.map fun i => P i ^ (e i + if i = a then 1 else 0)) = L.map fun i => P i ^ e i := by
        apply List.map_congr_left
        intro i hi
        have : i ≠ a := fun h => hL.1 (h ▸ hi)
        simp [this]
      rw [hrest]
      rw [if_pos rfl, pow_succ, mul_assoc, mul_assoc, ← (hcomm a).eq]
    · have hk' : k ∈ L := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h.symm hak
        · exact h
      rw [solution P hP e k L hL.2 hk']
      simp [hak, mul_assoc]
end PositivityTheory.Rg.Sw.LC.CoreBb
