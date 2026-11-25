-- Prove2me | solution 1 for PI.SqfRootShift.W.count_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:49.045636+00:00
-- url     : https://prove2.me/submissions/dd57a489-96b3-458f-a111-610c588dd9cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC
import Theorems.Thm_PI_SqfRootShift_W_card_ppRoots_le
import Theorems.Thm_PI_SqfRootShift_W_good_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
open Classical
namespace PI.SqfRootShift.W
theorem _root_.solution (c : (ZMod g)ˣ) (hg : 3 ≤ g) (k : ℕ) (hk : 1 ≤ k)
    (Q : Finset (ZMod g)[X]) (hQ : ∀ P ∈ Q, Good c P ∧ P.natDegree = k) :
    k * Q.card ≤ ppSum (g ^ k - 1) := by
  set alg := algebraMap (ZMod g) (Fbar g) with halg
  set c' := alg (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := (_root_.map_ne_zero _).2 c.ne_zero
  set R : (ZMod g)[X] → Finset (Fbar g) := fun P => (P.map alg).roots.toFinset with hRdef
  have hR : ∀ P ∈ Q, (R P).card = k := by
    intro P hP
    obtain ⟨⟨hmon, hirr, -⟩, hdeg⟩ := hQ P hP
    have hsep : (P.map alg).Separable := (PerfectField.separable_of_irreducible hirr).map
    rw [hRdef, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hdeg]
  have hdisj : (Q : Set (ZMod g)[X]).PairwiseDisjoint R := by
    intro P hP P' hP' hne
    refine Finset.disjoint_left.2 (fun z hz hz' => hne ?_)
    obtain ⟨⟨hmon, hirr, -⟩, -⟩ := hQ P hP
    obtain ⟨⟨hmon', hirr', -⟩, -⟩ := hQ P' hP'
    rw [hRdef, Multiset.mem_toFinset, mem_roots_map hmon.ne_zero] at hz
    rw [hRdef, Multiset.mem_toFinset, mem_roots_map hmon'.ne_zero] at hz'
    rw [minpoly.eq_of_irreducible_of_monic (A := ZMod g) (x := z) hirr
        (by rw [aeval_def]; exact hz) hmon,
      minpoly.eq_of_irreducible_of_monic (A := ZMod g) (x := z) hirr'
        (by rw [aeval_def]; exact hz') hmon']
  have hcard : (Q.biUnion R).card = k * Q.card := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hR, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hgk : g ≤ g ^ k := Nat.le_self_pow (by omega) g
  have hN : 2 ≤ g ^ k - 1 := by omega
  rw [← hcard]
  refine le_trans ?_ (card_ppRoots_le (K := Fbar g) (g ^ k - 1) hN)
  refine Finset.card_le_card_of_injOn (fun z => z * c'⁻¹) ?_ ?_
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_biUnion] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    obtain ⟨hgood, hdeg⟩ := hQ P hP
    rw [hRdef, Multiset.mem_toFinset] at hzP
    have h := good_root c P hgood z hzP
    rw [hdeg] at h
    rw [Finset.mem_coe, Finset.mem_filter, Polynomial.mem_nthRootsFinset (by omega)]
    exact h
  · intro z1 _ z2 _ h
    exact mul_right_cancel₀ (inv_ne_zero hc0) h
end PI.SqfRootShift.W
