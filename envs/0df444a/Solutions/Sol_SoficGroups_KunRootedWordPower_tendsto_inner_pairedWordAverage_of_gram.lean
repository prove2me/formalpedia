-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.tendsto_inner_pairedWordAverage_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/372d79af-7975-4d7b-903a-ba5ca57e7f85

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_inner_smul_fintype_sum

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {G ι N H : Type*} [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E : N → Type*}
    [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℂ (E n)]
    (l : Filter N) (s : ι → G)
    (z : ∀ n, G × G → E n) (v : G × G → H)
    (hgram : ∀ q r,
      Tendsto (fun n => ⟪z n q, z n r⟫_ℂ) l
        (𝓝 ⟪v q, v r⟫_ℂ))
    (k : ℕ) (q r : G × G) :
    Tendsto
      (fun n =>
        ⟪pairedWordAverage s (z n) k q,
          pairedWordAverage s (z n) k r⟫_ℂ)
      l
      (𝓝 ⟪pairedWordAverage s v k q,
        pairedWordAverage s v k r⟫_ℂ) := by
  induction k generalizing q r with
  | zero =>
      simpa [pairedWordAverage] using hgram q r
  | succ k ih =>
      have hsum :
          Tendsto
            (fun n =>
              ∑ i : ι, ∑ j : ι,
                ⟪pairedWordAverage s (z n) k
                    (s i * q.1, s i * q.2),
                  pairedWordAverage s (z n) k
                    (s j * r.1, s j * r.2)⟫_ℂ)
            l
            (𝓝 (∑ i : ι, ∑ j : ι,
              ⟪pairedWordAverage s v k
                  (s i * q.1, s i * q.2),
                pairedWordAverage s v k
                  (s j * r.1, s j * r.2)⟫_ℂ)) :=
        tendsto_finsetSum Finset.univ fun i _ =>
          tendsto_finsetSum Finset.univ fun j _ =>
            ih (s i * q.1, s i * q.2)
              (s j * r.1, s j * r.2)
      simpa only [pairedWordAverage, inner_smul_fintype_sum] using
        (tendsto_const_nhds.mul hsum).mul tendsto_const_nhds
end SoficGroups.KunRootedWordPower
