-- Prove2me | solution 1 for SemAC02.Supplement.theorem_6_5_random_3cnf
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T11:59:41.684209+00:00
-- url     : https://prove2.me/submissions/d2e31584-2875-44a6-908d-3db156152111

import Definitions.Def_PCNonBool_nbrOn
import Mathlib
import Definitions.Def_SemAC02_Supplement_expansionRank
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Supplement_randCNF
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_selLift
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Theorems.Thm_SemAC02_Supplement_lemma_5_3_expansion_pseudo_reduction
import Theorems.Thm_SemAC02_Supplement_theorem_4_4_sps_size_bound
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Bounds

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MRandomThreeCNFProof
section
-- Inlined Solutions.P2MFiniteFamilyBoundary

set_option maxHeartbeats 1000000

namespace P2MProofComplexity.P2MFiniteFamilyBoundary

variable {I V : Type} [DecidableEq V] [DecidableEq I]

noncomputable def neighbors (C : I → Finset V) (J : Finset I) := J.biUnion C
noncomputable def multiplicity (C : I → Finset V) (J : Finset I) (v : V) := (J.filter (fun j => v∈C j)).card
noncomputable def boundary (C : I → Finset V) (J : Finset I) :=
  (neighbors C J).filter (fun v => multiplicity C J v=1)

theorem double_count (C : I → Finset V) (J : Finset I) :
    ∑ v∈neighbors C J, multiplicity C J v=∑ j∈J, (C j).card := by
  classical
  simp only [multiplicity,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←Finset.sum_filter]
  have he : (neighbors C J).filter (fun v => v∈C j)=C j := by
    ext v
    constructor
    · intro hv; exact (Finset.mem_filter.mp hv).2
    · intro hv; exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j,hj,hv⟩,hv⟩
  rw [he]

theorem boundary_bound (C : I → Finset V) (J : Finset I) :
    2*(neighbors C J).card ≤ (boundary C J).card+∑ j∈J, (C j).card := by
  classical
  have hpoint (v : V) (hv : v∈neighbors C J) :
      2 ≤ (if multiplicity C J v=1 then 1 else 0)+multiplicity C J v := by
    have hn : 1 ≤ multiplicity C J v := by
      obtain ⟨j,hj,hv⟩ := Finset.mem_biUnion.mp hv
      exact Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hv⟩⟩
    split_ifs <;> omega
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at hh
  rw [double_count] at hh
  have hB : (∑ v∈neighbors C J, if multiplicity C J v=1 then 1 else 0)=(boundary C J).card := by
    simp only [boundary,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hB] at hh
  simpa only [Nat.mul_comm] using hh

end P2MProofComplexity.P2MFiniteFamilyBoundary
end

section
-- Inlined Solutions.P2MBipartiteNeighborhoodExpansion

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MBipartiteNeighborhoodExpansion

open PCNonBool

noncomputable def neighbors {L R : Type} [Fintype R] [DecidableEq R] (G : BipGraph L R) (J : Finset L) : Finset R :=
  J.biUnion (nbrOn G Finset.univ)

def Expands {L R : Type} [Fintype R] [DecidableEq R] (G : BipGraph L R) (s a : ℝ) : Prop :=
  ∀ J : Finset L, (J.card : ℝ) ≤ s → a*(J.card : ℝ) ≤ ((neighbors G J).card : ℝ)

 theorem neighbors_mono {L R : Type} [Fintype R] [DecidableEq R] (G : BipGraph L R) {I J : Finset L} (hIJ : I⊆J) :
    neighbors G I⊆neighbors G J := by
  intro v hv
  obtain ⟨u,hu,hv⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨u,hIJ hu,hv⟩

 theorem neighbors_union {L R : Type} [Fintype R] [DecidableEq R] [DecidableEq L] (G : BipGraph L R) (I J : Finset L) :
    neighbors G (I∪J)=neighbors G I∪neighbors G J := by
  classical
  ext v
  simp only [neighbors,Finset.mem_biUnion,Finset.mem_union]
  aesop

 theorem mem_neighbors {L R : Type} [Fintype R] [DecidableEq R] (G : BipGraph L R) (J : Finset L) (v : R) :
    v∈neighbors G J ↔ ∃ u∈J, G.Adj u v := by
  classical
  simp only [neighbors,Finset.mem_biUnion,nbrOn,Finset.mem_filter,Finset.mem_univ,true_and]

end P2MProofComplexity.P2MBipartiteNeighborhoodExpansion
end

section
-- Inlined Solutions.P2MCleaningMaximalDeletion

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MCleaningMaximalDeletion

open P2MBipartiteNeighborhoodExpansion

 theorem exists_deletion {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (G : PCNonBool.BipGraph L R) (s : ℝ) (seed : Finset R) (hSeed : seed.Nonempty)
    (hSeedSmall : (seed.card : ℝ) ≤ s/32) (hExp : Expands G s (15/8)) :
    ∃ I : Finset L, ∃ A : Finset R,
      A=seed∪neighbors G I ∧ (I.card : ℝ) ≤ 8*seed.card ∧ (A.card : ℝ) ≤ 15*seed.card ∧
      I.card<A.card ∧ seed⊆A ∧ neighbors G I⊆A ∧
      ∀ J : Finset L, Disjoint I J → J.Nonempty → (J.card : ℝ) ≤ s/2 →
        (7/4 : ℝ)*J.card < ((neighbors G J\A).card : ℝ) := by
  classical
  have hq : 0 < seed.card := Finset.card_pos.mpr hSeed
  have hqR : (0 : ℝ)<seed.card := by exact_mod_cast hq
  have hs : 0 ≤ s := by linarith
  let F := (Finset.univ : Finset (Finset L)).filter (fun I => (I.card : ℝ) ≤ s ∧
    ((seed∪neighbors G I).card : ℝ) ≤ seed.card+(7/4 : ℝ)*I.card)
  have hF : F.Nonempty := by
    refine ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩⟩
    · simpa using hs
    · simp [neighbors]
  obtain ⟨I,hIF,hMax⟩ := Finset.exists_max_image F Finset.card hF
  obtain ⟨hIs,hAI⟩ := (Finset.mem_filter.mp hIF).2
  let A := seed∪neighbors G I
  have hNsub : neighbors G I⊆A := Finset.subset_union_right
  have hNcard : ((neighbors G I).card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hNsub
  have hIbound : (I.card : ℝ) ≤ 8*seed.card := by
    have hh := hExp I hIs
    change (A.card : ℝ) ≤ seed.card+(7/4 : ℝ)*I.card at hAI
    nlinarith
  have hAbound : (A.card : ℝ) ≤ 15*seed.card := by nlinarith
  have hSeedA : seed⊆A := Finset.subset_union_left
  have hApos : 0 < A.card := lt_of_lt_of_le hq (Finset.card_le_card hSeedA)
  have hStrict : I.card<A.card := by
    have hh := hExp I hIs
    by_cases hI : I.card=0
    · omega
    · have hIp : (0 : ℝ)<I.card := by exact_mod_cast (show 0 < I.card by omega)
      have hlt : (I.card : ℝ)<A.card := by nlinarith
      exact_mod_cast hlt
  refine ⟨I,A,rfl,hIbound,hAbound,hStrict,hSeedA,hNsub,?_⟩
  intro J hDisj hJ hJs
  by_contra hBad
  have hBad' : ((neighbors G J\A).card : ℝ) ≤ (7/4 : ℝ)*J.card := le_of_not_gt hBad
  have hUnion : (I∪J).card=I.card+J.card := Finset.card_union_of_disjoint hDisj
  have hUnionS : ((I∪J).card : ℝ) ≤ s := by rw [hUnion]; push_cast; linarith
  have hSub : seed∪neighbors G (I∪J)⊆A∪(neighbors G J\A) := by
    rw [neighbors_union]
    intro v hv
    simp only [Finset.mem_union,Finset.mem_sdiff] at hv ⊢
    dsimp [A]
    simp only [Finset.mem_union]
    by_cases hvA : v∈seed∪neighbors G I <;> simp_all
  have hCard : ((seed∪neighbors G (I∪J)).card : ℝ) ≤ (A.card : ℝ)+(neighbors G J\A).card := by
    exact_mod_cast (Finset.card_le_card hSub).trans (Finset.card_union_le _ _)
  have hUnionA : ((seed∪neighbors G (I∪J)).card : ℝ) ≤ seed.card+(7/4 : ℝ)*(I∪J).card := by
    rw [hUnion]
    push_cast
    nlinarith
  have hUnionF : I∪J∈F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hUnionS,hUnionA⟩
  have hSize := hMax (I∪J) hUnionF
  have hJpos := Finset.card_pos.mpr hJ
  omega

end P2MProofComplexity.P2MCleaningMaximalDeletion
end

section
-- Inlined Solutions.P2MFiniteDegreeQuantile

set_option maxHeartbeats 1000000

namespace P2MProofComplexity.P2MFiniteDegreeQuantile

theorem exists_seed {R : Type} [Fintype R] [DecidableEq R]
    (f : R → ℕ) (q : ℕ) (hq : q ≤ Fintype.card R) :
    ∃ seed : Finset R, seed.card = q ∧
      ∀ v ∉ seed, q * f v ≤ ∑ w : R, f w := by
  classical
  let F := (Finset.univ : Finset R).powersetCard q
  have hF : F.Nonempty := by
    obtain ⟨seed, _, hseed⟩ := Finset.exists_subset_card_eq
      (show q ≤ (Finset.univ : Finset R).card by simpa using hq)
    exact ⟨seed, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hseed⟩⟩
  obtain ⟨seed, hseed, hmax⟩ := Finset.exists_max_image F (fun A => ∑ w ∈ A, f w) hF
  have hcard := (Finset.mem_powersetCard.mp hseed).2
  refine ⟨seed, hcard, ?_⟩
  intro v hv
  have hpoint (w : R) (hw : w ∈ seed) : f v ≤ f w := by
    have hve : v ∉ seed.erase w := fun h => hv (Finset.mem_of_mem_erase h)
    have hwcard : (seed.erase w).card + 1 = q := by
      rw [Finset.card_erase_of_mem hw]
      have := Finset.card_pos.mpr ⟨w, hw⟩
      omega
    have hnew : insert v (seed.erase w) ∈ F := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hve]; omega⟩
    have hsum := hmax (insert v (seed.erase w)) hnew
    rw [Finset.sum_insert hve] at hsum
    have hold := Finset.sum_erase_add seed f hw
    omega
  calc
    q * f v = ∑ w ∈ seed, f v := by simp [hcard]
    _ ≤ ∑ w ∈ seed, f w := Finset.sum_le_sum hpoint
    _ ≤ ∑ w : R, f w := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end P2MProofComplexity.P2MFiniteDegreeQuantile
end

section
-- Inlined Solutions.P2MCleaningDegreeReduction

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MCleaningDegreeReduction

open PCNonBool P2MBipartiteNeighborhoodExpansion

noncomputable def rightDegree {L R : Type} [Fintype L] (G : BipGraph L R) (v : R) : ℕ :=
  (Finset.univ.filter (fun u => G.Adj u v)).card

theorem degree_sum {L R : Type} [Fintype L] [Fintype R] [DecidableEq R]
    (G : BipGraph L R) (hdeg : ∀ u, (nbrOn G Finset.univ u).card = 3) :
    ∑ v : R, rightDegree G v = 3 * Fintype.card L := by
  classical
  simp only [rightDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have he (u : L) : (∑ v : R, if G.Adj u v then 1 else 0) = 3 := by
    simpa only [nbrOn, Finset.card_eq_sum_ones, Finset.sum_filter] using hdeg u
  simp only [he, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

theorem neighbors_after {L R : Type} [Fintype R] [DecidableEq R]
    (G : BipGraph L R) (A : Finset R) (J : Finset L) :
    P2MFiniteFamilyBoundary.neighbors (nbrOn G (Finset.univ \ A)) J = neighbors G J \ A := by
  classical
  ext v
  simp only [P2MFiniteFamilyBoundary.neighbors, Finset.mem_biUnion, nbrOn,
    Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_neighbors]
  aesop

theorem exists_deletion {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (G : BipGraph L R) (α γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hm : (Fintype.card L : ℝ) ≤ α * Fintype.card R)
    (hlarge : 64 ≤ γ * Fintype.card R)
    (hdeg : ∀ u, (nbrOn G Finset.univ u).card = 3)
    (hExp : Expands G (γ * Fintype.card R) (15/8)) :
    ∃ I : Finset L, ∃ A : Finset R,
      (I.card : ℝ) ≤ γ * Fintype.card R / 4 ∧ I.card < A.card ∧
      (A.card : ℝ) < Fintype.card R / 2 ∧ neighbors G I ⊆ A ∧
      (∀ u ∉ I, 2 ≤ (nbrOn G (Finset.univ \ A) u).card ∧
        (nbrOn G (Finset.univ \ A) u).card ≤ 3) ∧
      (∀ v ∉ A, (rightDegree G v : ℝ) ≤ 192 * α / γ) ∧
      (∀ J : Finset L, Disjoint I J → J.Nonempty →
        (J.card : ℝ) ≤ γ * Fintype.card R / 2 →
        (7/4 : ℝ) * J.card < ((neighbors G J \ A).card : ℝ)) ∧
      (∀ J : Finset L, Disjoint I J → J.Nonempty →
        (J.card : ℝ) ≤ γ * Fintype.card R / 2 →
        (J.card : ℝ) / 2 <
          ((P2MFiniteFamilyBoundary.boundary (nbrOn G (Finset.univ \ A)) J).card : ℝ)) := by
  classical
  let n : ℝ := Fintype.card R
  let s := γ * n
  let q := ⌊s/32⌋₊
  have hs : 64 ≤ s := hlarge
  have hn : 0 < n := by dsimp [s] at hs; nlinarith
  have hsn : s ≤ n := by dsimp [s]; nlinarith
  have hqUpper : (q : ℝ) ≤ s/32 := Nat.floor_le (by linarith)
  have hqLower : s/64 ≤ q := by
    have hh := Nat.lt_floor_add_one (s/32)
    dsimp [q] at *
    linarith
  have hqPos : 0 < q := by
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this
  have hqn : q ≤ Fintype.card R := by
    have : (q : ℝ) ≤ n := by linarith
    dsimp [n] at this
    exact_mod_cast this
  obtain ⟨seed, hseedCard, hseedDeg⟩ := P2MFiniteDegreeQuantile.exists_seed (rightDegree G) q hqn
  have hseed : seed.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨I, A, hA, hI, hAbound, hIA, hseedA, hN, hStrict⟩ :=
    P2MCleaningMaximalDeletion.exists_deletion G s seed hseed (by simpa [hseedCard] using hqUpper) hExp
  have hIbound : (I.card : ℝ) ≤ s/4 := by rw [hseedCard] at hI; linarith
  have hAhalf : (A.card : ℝ) < n/2 := by rw [hseedCard] at hAbound; linarith
  have hleftUpper (u : L) : (nbrOn G (Finset.univ \ A) u).card ≤ 3 := by
    rw [← hdeg u]
    apply Finset.card_le_card
    intro v hv
    simp only [nbrOn, Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_univ _, hv.2⟩
  have hleft (u : L) (hu : u ∉ I) : 2 ≤ (nbrOn G (Finset.univ \ A) u).card := by
    have hd : Disjoint I {u} := by simpa using hu
    have hh := hStrict {u} hd (by simp) (by simp; dsimp [s] at hs ⊢; linarith)
    have he : neighbors G {u} \ A = nbrOn G (Finset.univ \ A) u := by
      ext v
      simp [mem_neighbors, nbrOn, and_comm]
    rw [he] at hh
    simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hh
    have : (1 : ℝ) < (nbrOn G (Finset.univ \ A) u).card := by linarith
    exact_mod_cast this
  refine ⟨I, A, hIbound, hIA, hAhalf, hN, (fun u hu => ⟨hleft u hu, hleftUpper u⟩), ?_, hStrict, ?_⟩
  · intro v hv
    have hvseed : v ∉ seed := fun hh => hv (hseedA hh)
    have hh := hseedDeg v hvseed
    rw [degree_sum G hdeg] at hh
    have hhR : (q : ℝ) * rightDegree G v ≤ 3 * Fintype.card L := by exact_mod_cast hh
    apply (le_div_iff₀ hγ).mpr
    have hlower : s / 64 * rightDegree G v ≤ (q : ℝ) * rightDegree G v :=
      mul_le_mul_of_nonneg_right hqLower (Nat.cast_nonneg _)
    dsimp [s, n] at *
    nlinarith
  · intro J hDisj hJ hJs
    have hNstrict := hStrict J hDisj hJ hJs
    have hb := P2MFiniteFamilyBoundary.boundary_bound (nbrOn G (Finset.univ \ A)) J
    have hsum : (∑ u ∈ J, (nbrOn G (Finset.univ \ A) u).card) ≤ 3 * J.card := by
      calc
        _ ≤ ∑ u ∈ J, 3 := Finset.sum_le_sum (fun u _ => hleftUpper u)
        _ = _ := by simp [Nat.mul_comm]
    rw [neighbors_after] at hb
    have hbR : 2 * ((neighbors G J \ A).card : ℝ) ≤
        ((P2MFiniteFamilyBoundary.boundary (nbrOn G (Finset.univ \ A)) J).card : ℝ) + 3 * J.card := by
      exact_mod_cast (hb.trans (Nat.add_le_add_left hsum _))
    nlinarith

end P2MProofComplexity.P2MCleaningDegreeReduction
end

section
-- Inlined Solutions.P2MPrimalGraphBalls

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MPrimalGraphBalls

open PCNonBool

variable {L V : Type} [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V]

noncomputable def adjacent (G : BipGraph L V) (v : V) : Finset V :=
  (Finset.univ.filter (fun u => G.Adj u v)).biUnion (fun u => (nbrOn G Finset.univ u).erase v)

theorem mem_adjacent (G : BipGraph L V) (v w : V) :
    w ∈ adjacent G v ↔ w ≠ v ∧ ∃ u, G.Adj u v ∧ G.Adj u w := by
  simp only [adjacent, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, nbrOn]
  aesop

theorem adjacent_symm (G : BipGraph L V) (v w : V) (h : w ∈ adjacent G v) : v ∈ adjacent G w := by
  obtain ⟨hne, u, hv, hw⟩ := (mem_adjacent G v w).mp h
  exact (mem_adjacent G w v).mpr ⟨hne.symm, u, hw, hv⟩

theorem adjacent_card (G : BipGraph L V) (d : ℕ)
    (hL : ∀ u, (nbrOn G Finset.univ u).card ≤ 3)
    (hR : ∀ v, P2MCleaningDegreeReduction.rightDegree G v ≤ d) (v : V) :
    (adjacent G v).card ≤ 2*d := by
  have herase (u : L) (hu : u ∈ Finset.univ.filter (fun u => G.Adj u v)) :
      ((nbrOn G Finset.univ u).erase v).card ≤ 2 := by
    have hv : v ∈ nbrOn G Finset.univ u :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
    rw [Finset.card_erase_of_mem hv]
    have hh := hL u
    omega
  calc
    _ ≤ ∑ u ∈ Finset.univ.filter (fun u => G.Adj u v), ((nbrOn G Finset.univ u).erase v).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ u ∈ Finset.univ.filter (fun u => G.Adj u v), 2 := Finset.sum_le_sum herase
    _ = 2 * P2MCleaningDegreeReduction.rightDegree G v := by simp [P2MCleaningDegreeReduction.rightDegree, Nat.mul_comm]
    _ ≤ 2*d := Nat.mul_le_mul_left _ (hR v)

noncomputable def ball (G : BipGraph L V) : ℕ → V → Finset V
  | 0, v => {v}
  | r+1, v => insert v ((adjacent G v).biUnion (ball G r))

theorem self_mem (G : BipGraph L V) (r : ℕ) (v : V) : v ∈ ball G r v := by
  cases r <;> simp [ball]

theorem mono_succ (G : BipGraph L V) (r : ℕ) (v : V) : ball G r v ⊆ ball G (r+1) v := by
  induction r generalizing v with
  | zero =>
    intro w hw
    have he : w = v := by simpa only [ball, Finset.mem_singleton] using hw
    subst w
    exact self_mem G 1 v
  | succ r ih =>
    intro w hw
    rcases Finset.mem_insert.mp hw with he | hw
    · subst w; exact self_mem G _ v
    · obtain ⟨x, hx, hw⟩ := Finset.mem_biUnion.mp hw
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, hx, ih x hw⟩)

theorem step_right (G : BipGraph L V) (r : ℕ) (v x w : V)
    (hx : x ∈ ball G r v) (hxw : w ∈ adjacent G x) : w ∈ ball G (r+1) v := by
  induction r generalizing v x with
  | zero =>
    have he : x = v := by simpa only [ball, Finset.mem_singleton] using hx
    subst x
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨w, hxw, self_mem G 0 w⟩)
  | succ r ih =>
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨w, hxw, self_mem G (r+1) w⟩)
    · obtain ⟨y, hy, hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨y, hy, ih y x hx hxw⟩)

theorem ball_symm (G : BipGraph L V) (r : ℕ) (v w : V) (hw : w ∈ ball G r v) : v ∈ ball G r w := by
  induction r generalizing v w with
  | zero => simpa only [ball, Finset.mem_singleton, eq_comm] using hw
  | succ r ih =>
    rcases Finset.mem_insert.mp hw with he | hw
    · subst w; exact self_mem G _ v
    · obtain ⟨x, hx, hw⟩ := Finset.mem_biUnion.mp hw
      exact step_right G r w x v (ih x w hw) (adjacent_symm G v x hx)

theorem common_step (G : BipGraph L V) (r : ℕ) (v x w : V) (u : L)
    (hx : x ∈ ball G r v) (hux : G.Adj u x) (huw : G.Adj u w) : w ∈ ball G (r+1) v := by
  by_cases he : w = x
  · subst w; exact mono_succ G r v hx
  · exact step_right G r v x w hx ((mem_adjacent G x w).mpr ⟨he, u, hux, huw⟩)

theorem ball_card (G : BipGraph L V) (δ : ℕ) (hδ : ∀ v, (adjacent G v).card ≤ δ) :
    ∀ r v, (ball G r v).card ≤ ∑ i ∈ Finset.range (r+1), δ^i := by
  intro r
  induction r with
  | zero => intro v; simp [ball]
  | succ r ih =>
    intro v
    have hsum : (∑ i ∈ Finset.range (r+2), δ^i) = 1 + δ * ∑ i ∈ Finset.range (r+1), δ^i := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, pow_succ', ← Finset.mul_sum]
      omega
    rw [hsum]
    calc
      _ ≤ 1 + ((adjacent G v).biUnion (ball G r)).card := by
        exact (Finset.card_insert_le _ _).trans_eq (Nat.add_comm _ _)
      _ ≤ 1 + ∑ x ∈ adjacent G v, (ball G r x).card := Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ 1 + ∑ x ∈ adjacent G v, (∑ i ∈ Finset.range (r+1), δ^i) :=
        Nat.add_le_add_left (Finset.sum_le_sum (fun x _ => ih x)) _
      _ = 1 + (adjacent G v).card * ∑ i ∈ Finset.range (r+1), δ^i := by simp
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ (hδ v)) _

theorem radius_three_card (G : BipGraph L V) (d : ℕ)
    (hL : ∀ u, (nbrOn G Finset.univ u).card ≤ 3)
    (hR : ∀ v, P2MCleaningDegreeReduction.rightDegree G v ≤ d) (v : V) :
    (ball G 3 v).card ≤ 1 + 2*d + (2*d)^2 + (2*d)^3 := by
  simpa [Finset.sum_range_succ] using ball_card G (2*d) (adjacent_card G d hL hR) 3 v

end P2MProofComplexity.P2MPrimalGraphBalls
end

section
-- Inlined Solutions.P2MSeparatedSetCounting

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MSeparatedSetCounting

variable {V : Type} [Fintype V] [DecidableEq V]

def Good (B : V → Finset V) (A : Finset V) : Prop :=
  ∀ v ∈ A, ∀ w ∈ A, v ≠ w → w ∉ B v

noncomputable def sets (B : V → Finset V) (j : ℕ) : Finset (Finset V) :=
  open Classical in Finset.univ.filter (fun A => A.card = j ∧ Good B A)

noncomputable def available (B : V → Finset V) (A : Finset V) : Finset V :=
  Finset.univ \ A.biUnion B

theorem mem_sets (B : V → Finset V) (j : ℕ) (A : Finset V) :
    A ∈ sets B j ↔ A.card = j ∧ Good B A := by
  classical
  simp [sets]

theorem available_bound (B : V → Finset V) (b : ℕ) (hB : ∀ v, (B v).card ≤ b)
    (A : Finset V) : Fintype.card V - b * A.card ≤ (available B A).card := by
  have hcard : (A.biUnion B).card ≤ b * A.card := by
    calc
      _ ≤ ∑ v ∈ A, (B v).card := Finset.card_biUnion_le
      _ ≤ ∑ v ∈ A, b := Finset.sum_le_sum (fun v _ => hB v)
      _ = _ := by simp [Nat.mul_comm]
  dsimp only [available]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  omega

theorem available_not_mem (B : V → Finset V) (hself : ∀ v, v ∈ B v)
    (A : Finset V) (v : V) (hv : v ∈ available B A) : v ∉ A := by
  intro hvA
  exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨v, hvA, hself v⟩)

theorem good_insert (B : V → Finset V)
    (hsymm : ∀ v w, w ∈ B v → v ∈ B w) (A : Finset V) (hA : Good B A)
    (v : V) (hv : v ∈ available B A) : Good B (insert v A) := by
  intro x hx y hy hxy
  have hav (w : V) (hw : w ∈ A) : v ∉ B w := by
    intro hh
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨w, hw, hh⟩)
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    rcases Finset.mem_insert.mp hy with hy | hy
    · exact (hxy hy.symm).elim
    · exact fun hh => hav y hy (hsymm v y hh)
  · rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      exact hav x hx
    · exact hA x hx y hy hxy

theorem step (B : V → Finset V) (b : ℕ) (hB : ∀ v, (B v).card ≤ b)
    (hself : ∀ v, v ∈ B v) (hsymm : ∀ v w, w ∈ B v → v ∈ B w) (j : ℕ) :
    (Fintype.card V - b*j) * (sets B j).card ≤ (j+1) * (sets B (j+1)).card := by
  classical
  let D := (Σ A : sets B j, {v // v ∈ available B A.val})
  let T := (Σ A : sets B (j+1), A.val)
  have hnot (A : sets B j) (v : {v // v ∈ available B A.val}) : v.val ∉ A.val :=
    available_not_mem B hself A.val v.val v.property
  have hnew (A : sets B j) (v : {v // v ∈ available B A.val}) :
      insert v.val A.val ∈ sets B (j+1) := by
    apply (mem_sets B _ _).mpr
    obtain ⟨hcard, hgood⟩ := (mem_sets B _ _).mp A.property
    exact ⟨by rw [Finset.card_insert_of_notMem (hnot A v), hcard],
      good_insert B hsymm A.val hgood v.val v.property⟩
  let f : D → T := fun z =>
    ⟨⟨insert z.2.val z.1.val, hnew z.1 z.2⟩, ⟨z.2.val, Finset.mem_insert_self _ _⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨A, v⟩ ⟨A', v'⟩ he
    have hv : v.val = v'.val := congrArg (fun z : T => z.2.val) he
    have hset : insert v.val A.val = insert v'.val A'.val := congrArg (fun z : T => z.1.val) he
    have heA : A.val = A'.val := by
      have hh := congrArg (fun E => E.erase v.val) hset
      have hnot' : v.val ∉ A'.val := by rw [hv]; exact hnot A' v'
      rw [← hv, Finset.erase_insert (hnot A v), Finset.erase_insert hnot'] at hh
      exact hh
    have heA' : A = A' := Subtype.ext heA
    subst A'
    have hev : v = v' := Subtype.ext hv
    subst v'
    rfl
  have hT (A : sets B (j+1)) : Fintype.card A.val = j+1 := by
    rw [Fintype.card_coe]
    exact ((mem_sets B _ _).mp A.property).1
  calc
    _ = ∑ A : sets B j, (Fintype.card V - b*j) := by simp [Nat.mul_comm]
    _ ≤ ∑ A : sets B j, Fintype.card {v // v ∈ available B A.val} := by
      apply Finset.sum_le_sum
      intro A hA
      rw [Fintype.card_coe]
      have hh := available_bound B b hB A.val
      rwa [((mem_sets B _ _).mp A.property).1] at hh
    _ = Fintype.card D := (Fintype.card_sigma).symm
    _ ≤ Fintype.card T := Fintype.card_le_of_injective f hf
    _ = _ := by rw [Fintype.card_sigma]; simp [hT, Nat.mul_comm]

theorem count (B : V → Finset V) (b : ℕ) (hB : ∀ v, (B v).card ≤ b)
    (hself : ∀ v, v ∈ B v) (hsymm : ∀ v w, w ∈ B v → v ∈ B w) (k : ℕ) :
    (Fintype.card V - b*(k-1))^k ≤ k.factorial * (sets B k).card := by
  classical
  let q := Fintype.card V - b*(k-1)
  have hbase : sets B 0 = {∅} := by
    ext A
    rw [mem_sets, Finset.mem_singleton]
    constructor
    · exact fun h => Finset.card_eq_zero.mp h.1
    · intro he
      subst A
      simp [Good]
  have hi : ∀ j ≤ k, q^j ≤ j.factorial * (sets B j).card := by
    intro j
    induction j with
    | zero => simp [hbase]
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hstep := step B b hB hself hsymm j
      have hq : q ≤ Fintype.card V - b*j := by
        have hh := Nat.mul_le_mul_left b (show j ≤ k-1 by omega)
        dsimp [q]
        omega
      calc
        q^(j+1) = q^j*q := pow_succ _ _
        _ ≤ (j.factorial * (sets B j).card)*q := Nat.mul_le_mul_right _ hprev
        _ ≤ j.factorial * ((Fintype.card V-b*j)*(sets B j).card) := by
          have hh := Nat.mul_le_mul_left (j.factorial * (sets B j).card) hq
          nlinarith
        _ ≤ j.factorial * ((j+1)*(sets B (j+1)).card) := Nat.mul_le_mul_left _ hstep
        _ = (j+1).factorial * (sets B (j+1)).card := by rw [Nat.factorial_succ]; ring
  exact hi k le_rfl

end P2MProofComplexity.P2MSeparatedSetCounting
end

section
-- Inlined Solutions.P2MBoundaryAvoidance

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBoundaryAvoidance

open PCNonBool

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def Avoiding (G : BipGraph L R) (s : ℝ) (A : Finset R) : Prop :=
  ∀ J : Finset L, J.Nonempty → (J.card : ℝ) ≤ s → ¬ boundaryOn G Finset.univ J⊆A

theorem sup_eq_empty (G : BipGraph L R) (s : ℝ) (A : Finset R) (hA : Avoiding G s A) : supS G s A=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨J,hJ,huJ⟩ := Finset.mem_biUnion.mp hu
  have hh := (Finset.mem_filter.mp hJ).2
  exact hA J ⟨u,huJ⟩ hh.1 hh.2

theorem avoiding_of_sup_empty (G : BipGraph L R) (s : ℝ) (A : Finset R) (hA : supS G s A=∅) :
    Avoiding G s A := by
  classical
  intro J hJ hsize hsub
  obtain ⟨u,hu⟩ := hJ
  have hm : u∈supS G s A := Finset.mem_biUnion.mpr
    ⟨J,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsize,hsub⟩,hu⟩
  rw [hA] at hm
  simpa using hm

end SemAC02.Supplement.P2MBoundaryAvoidance
end

section
-- Inlined Solutions.P2MPrimalBoundaryAvoidance

set_option maxHeartbeats 4000000

namespace P2MProofComplexity.P2MPrimalBoundaryAvoidance

open PCNonBool P2MPrimalGraphBalls

variable {L V : Type} [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V]

theorem pair_exists (G : BipGraph L V) (hL : ∀ u, 2 ≤ (nbrOn G Finset.univ u).card)
    (J : Finset L) (A : Finset V)
    (hA : P2MSeparatedSetCounting.Good (ball G 3) A)
    (hBA : boundaryOn G Finset.univ J ⊆ A)
    (v : V) (hv : v ∈ boundaryOn G Finset.univ J) :
    ∃ u w : L, ∃ x : V, u ∈ J ∧ w ∈ J ∧ u ≠ w ∧
      G.Adj u v ∧ G.Adj u x ∧ G.Adj w x := by
  classical
  obtain ⟨u, hsingle⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hv).2
  have hu : u ∈ J.filter (fun u => G.Adj u v) := by rw [hsingle]; simp
  obtain ⟨huJ, huv⟩ := Finset.mem_filter.mp hu
  have hvN : v ∈ nbrOn G Finset.univ u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩
  have hxExists : ((nbrOn G Finset.univ u).erase v).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hvN]
    have hh := hL u
    omega
  obtain ⟨x, hx⟩ := hxExists
  obtain ⟨hxv, hxN⟩ := Finset.mem_erase.mp hx
  have hux := (Finset.mem_filter.mp hxN).2
  have hxB : x ∉ boundaryOn G Finset.univ J := by
    intro hxB
    have hpath1 := common_step G 0 v v x u (self_mem G 0 v) huv hux
    have hpath3 := mono_succ G 2 v (mono_succ G 1 v hpath1)
    exact hA v (hBA hv) x (hBA hxB) hxv.symm hpath3
  have hwExists : ∃ w ∈ J, w ≠ u ∧ G.Adj w x := by
    by_contra hn
    have he : J.filter (fun w => G.Adj w x) = {u} := by
      ext w
      constructor
      · intro hw
        obtain ⟨hwJ, hwx⟩ := Finset.mem_filter.mp hw
        have hwu : w = u := by
          by_contra hne
          exact hn ⟨w, hwJ, hne, hwx⟩
        exact Finset.mem_singleton.mpr hwu
      · intro hw
        have he := Finset.mem_singleton.mp hw
        subst w
        exact Finset.mem_filter.mpr ⟨huJ, hux⟩
    apply hxB
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [he, Finset.card_singleton]⟩
  obtain ⟨w, hwJ, hwu, hwx⟩ := hwExists
  exact ⟨u, w, x, huJ, hwJ, hwu.symm, huv, hux, hwx⟩

theorem boundary_at_most_half (G : BipGraph L V)
    (hL : ∀ u, 2 ≤ (nbrOn G Finset.univ u).card) (J : Finset L) (A : Finset V)
    (hA : P2MSeparatedSetCounting.Good (ball G 3) A)
    (hBA : boundaryOn G Finset.univ J ⊆ A) :
    2 * (boundaryOn G Finset.univ J).card ≤ J.card := by
  classical
  let B := boundaryOn G Finset.univ J
  have hpairs (v : B) := pair_exists G hL J A hA hBA v.val v.property
  choose u w x hu hw hne huv hux hwx using hpairs
  let pick (v : B) (b : Bool) : L := if b then u v else w v
  let point (v : B) (b : Bool) : V := if b then v.val else x v
  have hpickJ (v : B) (b : Bool) : pick v b ∈ J := by cases b <;> simp [pick, hu, hw]
  have hpoint (v : B) (b : Bool) : G.Adj (u v) (point v b) := by cases b <;> simp [point, huv, hux]
  have hpick (v : B) (b : Bool) : G.Adj (pick v b) (point v b) := by cases b <;> simp [pick, point, huv, hwx]
  let f : B × Bool → J := fun z => ⟨pick z.1 z.2, hpickJ z.1 z.2⟩
  have hf : Function.Injective f := by
    rintro ⟨v, b⟩ ⟨v', b'⟩ he
    have hsame : pick v b = pick v' b' := congrArg Subtype.val he
    have hvv : v.val = v'.val := by
      by_contra hvv
      have hpath1 := common_step G 0 v.val v.val (point v b) (u v)
        (self_mem G 0 v.val) (huv v) (hpoint v b)
      have hpath2 := common_step G 1 v.val (point v b) (point v' b') (pick v b)
        hpath1 (hpick v b) (by rw [hsame]; exact hpick v' b')
      have hpath3 := common_step G 2 v.val (point v' b') v'.val (u v')
        hpath2 (hpoint v' b') (huv v')
      exact hA v.val (hBA v.property) v'.val (hBA v'.property) hvv hpath3
    have heV : v = v' := Subtype.ext hvv
    subst v'
    have heB : b = b' := by
      cases b <;> cases b'
      · rfl
      · have hh : w v = u v := by simpa [pick] using hsame
        exact (hne v hh.symm).elim
      · have hh : u v = w v := by simpa [pick] using hsame
        exact (hne v hh).elim
      · rfl
    subst b'
    rfl
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Nat.mul_comm] using hh

theorem avoiding (G : BipGraph L V) (s : ℝ)
    (hL : ∀ u, 2 ≤ (nbrOn G Finset.univ u).card)
    (hstrict : ∀ J : Finset L, J.Nonempty → (J.card : ℝ) ≤ s →
      (J.card : ℝ)/2 < ((boundaryOn G Finset.univ J).card : ℝ))
    (A : Finset V) (hA : P2MSeparatedSetCounting.Good (ball G 3) A) :
    SemAC02.Supplement.P2MBoundaryAvoidance.Avoiding G s A := by
  intro J hJ hJs hBA
  have hh := boundary_at_most_half G hL J A hA hBA
  have hhR : 2 * ((boundaryOn G Finset.univ J).card : ℝ) ≤ J.card := by exact_mod_cast hh
  have hbound := hstrict J hJ hJs
  linarith

end P2MProofComplexity.P2MPrimalBoundaryAvoidance
end

section
-- Inlined Solutions.P2MBooleanAlgebra

open MvPolynomial AC02Frege
namespace AC02Frege.P2MBooleanAlgebra

theorem ml_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl]
  rw [h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem ml_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (ML p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial]
    intro t ht v
    have ht' : t = sqfree s := (Finset.mem_singleton.mp (support_monomial_subset ht))
    subst t
    simp [sqfree, Finsupp.mapRange_apply]
  | add p q hp hq =>
    rw [map_add]
    intro s hs v
    rcases Finset.mem_union.mp (support_add hs) with hs | hs
    · exact hp s hs v
    · exact hq s hs v


theorem sqfree_support {V : Type*} (s : V →₀ ℕ) : (sqfree s).support = s.support := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, sqfree, Finsupp.mapRange_apply]
  omega

theorem sqfree_eq_self {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) : sqfree s = s := by
  ext i
  simp only [sqfree, Finsupp.mapRange_apply, min_eq_left (hs i)]

theorem ml_of_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : ML p = p := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [sqfree_eq_self s (hp s hs)]

theorem ml_idempotent {V : Type*} (p : MvPolynomial V (ZMod 2)) : ML (ML p) = ML p :=
  ml_of_multilinear _ (ml_multilinear p)

theorem eval_ml {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (ML p) = eval x p := by
  classical
  have hpow (a : ZMod 2) (k : ℕ) : a ^ min k 1 = a ^ k := by
    fin_cases a
    · change (0 : ZMod 2) ^ min k 1 = (0 : ZMod 2) ^ k
      cases k <;> simp
    · change (1 : ZMod 2) ^ min k 1 = (1 : ZMod 2) ^ k
      simp
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial, eval_monomial, eval_monomial]
    congr 1
    simp only [Finsupp.prod, sqfree_support]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [sqfree, Finsupp.mapRange_apply] using hpow (x i) (s i)
  | add p q hp hq => simp only [map_add, hp, hq]

theorem multilinear_ext {V : Type} [Finite V]
    {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (h : ∀ x : V → ZMod 2, eval x p = eval x q) : p = q := by
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero V (ZMod 2) (p - q)
  · intro x; simp only [map_sub, h x, sub_self]
  · have hp' : p ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V p 1).mpr hp
    have hq' : q ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V q 1).mpr hq
    simpa only [ZMod.card, Nat.reduceSub] using (restrictDegree V (ZMod 2) 1).sub_mem hp' hq'

theorem ml_mul_left {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (ML p * q) = ML (p * q) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [eval_ml, map_mul]

theorem ml_mul_right {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (p * ML q) = ML (p * q) := by
  rw [mul_comm p (ML q), ml_mul_left, mul_comm]

theorem xMon_eq_monomial {V : Type*} (S : Finset V) :
    xMon S = monomial (Finsupp.indicator S (fun _ _ => 1)) (1 : ZMod 2) := by
  classical
  simpa only [xMon, pow_one] using (prod_X_pow (R := ZMod 2) (fun _ : V => 1) S)

theorem indicator_support {V : Type*} (S : Finset V) :
    (Finsupp.indicator S (fun _ _ => (1 : ℕ))).support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, Finsupp.indicator_apply]
  split_ifs <;> simp_all

theorem xMon_multilinear {V : Type*} (S : Finset V) : IsMultilinear (xMon S) := by
  classical
  rw [xMon_eq_monomial]
  intro s hs i
  have heq := Finset.mem_singleton.mp (support_monomial_subset hs)
  subst s
  simp only [Finsupp.indicator_apply]
  split_ifs <;> omega

theorem xMon_eval {V : Type*} (S : Finset V) (x : V → ZMod 2) :
    eval x (xMon S) = ∏ i ∈ S, x i := by
  simp only [xMon, map_prod, eval_X]

theorem xMon_totalDegree {V : Type*} (S : Finset V) : (xMon S).totalDegree = S.card := by
  classical
  rw [xMon_eq_monomial, totalDegree_monomial _ (one_ne_zero : (1 : ZMod 2) ≠ 0)]
  simp only [Finsupp.sum, indicator_support]
  have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finsupp.indicator_apply, hi]
  rw [heq]
  simp

theorem xMon_linearIndependent {V : Type*} :
    LinearIndependent (ZMod 2) (fun S : Finset V => xMon S) := by
  classical
  have hinj : Function.Injective (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) := by
    intro S T h
    have := congrArg Finsupp.support h
    simpa only [indicator_support] using this
  have h := (basisMonomials V (ZMod 2)).linearIndependent.comp
    (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) hinj
  simpa only [Function.comp_def, coe_basisMonomials, xMon_eq_monomial] using h

end AC02Frege.P2MBooleanAlgebra
end

section
-- Inlined Solutions.P2MMajorityFoundation

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace AC02Frege.P2MMajorityFoundation

open Classical

noncomputable def pointPoly {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) : MvPolynomial V (ZMod 2) :=
  ∏ i : V, if i ∈ S then X i else 1 + X i

theorem pointPoly_indicator {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = MvPolynomial.indicator (fun i : V => if i ∈ S then (1 : ZMod 2) else 0) := by
  classical
  unfold pointPoly MvPolynomial.indicator
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp only [hi, ↓reduceIte, ZMod.card, Nat.reduceSub, pow_one]
  · simp only [map_one, CharTwo.sub_eq_add]
    calc
      X i = X i + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + (X i + 1) := by abel
  · simp [CharTwo.sub_eq_add]

theorem pointPoly_multilinear {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    IsMultilinear (pointPoly S) := by
  rw [pointPoly_indicator]
  apply (mem_restrictDegree V _ 1).mp
  simpa only [ZMod.card, Nat.reduceSub] using indicator_mem_restrictDegree
    (fun i : V => if i ∈ S then (1 : ZMod 2) else 0)

theorem pointPoly_eval {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (x : V → ZMod 2) :
    eval x (pointPoly S) =
      if x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) then 1 else 0 := by
  classical
  rw [pointPoly_indicator]
  split_ifs with h
  · subst x; exact eval_indicator_apply_eq_one _
  · exact eval_indicator_apply_eq_zero _ _ h

theorem multilinear_sum {V ι : Type} (S : Finset ι) (f : ι → MvPolynomial V (ZMod 2))
    (hf : ∀ i ∈ S, IsMultilinear (f i)) : IsMultilinear (∑ i ∈ S, f i) := by
  apply (mem_restrictDegree V _ 1).mp
  exact Submodule.sum_mem _ (fun i hi => (mem_restrictDegree V (f i) 1).mpr (hf i hi))

theorem majOne_multilinear (ℓ : ℕ) : IsMultilinear (majOne ℓ) := by
  unfold majOne
  apply multilinear_sum
  intro S _
  simpa only [pointPoly] using pointPoly_multilinear S

theorem eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem point_of_ones {V : Type} [Fintype V] [DecidableEq V] (x : V → ZMod 2) :
    (fun i => if i ∈ Finset.univ.filter (fun i => x i = 1) then (1 : ZMod 2) else 0) = x := by
  classical
  funext i
  rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]

theorem ones_of_point {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    Finset.univ.filter (fun i => (if i ∈ S then (1 : ZMod 2) else 0) = 1) = S := by
  classical
  ext i
  simp

theorem majOne_eval (ℓ : ℕ) (x : Fin ℓ → ZMod 2) :
    eval x (majOne ℓ) = if ℓ / 2 < (Finset.univ.filter (fun i => x i = 1)).card
      then 1 else 0 := by
  classical
  unfold majOne
  simp only [map_sum]
  have hev (S : Finset (Fin ℓ)) := pointPoly_eval S x
  simp only [pointPoly] at hev
  simp only [hev]
  have heq (S : Finset (Fin ℓ)) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro hx; rw [hx, ones_of_point]
    · intro hS; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp

theorem heavy_monomial_absorbs_majority (ℓ : ℕ) (S : Finset (Fin ℓ))
    (hS : ℓ / 2 < S.card) : ML (xMon S * majOne ℓ) = xMon S := by
  apply multilinear_ext (ml_multilinear _) (xMon_multilinear S)
  intro x
  simp only [eval_ml, map_mul]
  by_cases hx : eval x (xMon S) = 0
  · rw [hx, zero_mul]
  · have hsub : S ⊆ Finset.univ.filter (fun i => x i = 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxi : x i ≠ 0 := by
        intro hz
        apply hx
        rw [xMon_eval]
        exact Finset.prod_eq_zero hi hz
      rcases eq_zero_or_one (x i) with hz | ho
      · exact False.elim (hxi hz)
      · exact ho
    have hcard := Finset.card_le_card hsub
    rw [majOne_eval, if_pos (by omega), mul_one]

theorem pointPoly_factor {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = xMon S * ∏ i ∈ Finset.univ.filter (fun i : V => i ∉ S),
      (1 + X i : MvPolynomial V (ZMod 2)) := by
  simp only [pointPoly, Finset.prod_ite]
  congr 1
  rw [xMon]
  apply Finset.prod_congr
  · ext i; simp
  · intro i _; rfl

theorem support_mul_xMon_degree {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (p : MvPolynomial V (ZMod 2))
    (s : V →₀ ℕ) (hs : s ∈ (xMon S * p).support) : S.card ≤ s.sum (fun _ e => e) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul (xMon S) p hs)
  have haeq : a = Finsupp.indicator S (fun _ _ => (1 : ℕ)) := by
    rw [xMon_eq_monomial] at ha
    exact Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  have hsum : (Finsupp.indicator S (fun _ _ => (1 : ℕ))).sum (fun _ e => e) = S.card := by
    simp only [Finsupp.sum, indicator_support]
    have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finsupp.indicator_apply, hi]
    rw [heq]; simp
  rw [← hab]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hsum]
  omega

theorem majOne_support_heavy (ℓ : ℕ) (s : Fin ℓ →₀ ℕ)
    (hs : s ∈ (majOne ℓ).support) : ℓ / 2 < s.sum (fun _ e => e) := by
  classical
  unfold majOne at hs
  obtain ⟨S, hS, hsS⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have hheavy := (Finset.mem_filter.mp hS).2
  change s ∈ (pointPoly S).support at hsS
  rw [pointPoly_factor] at hsS
  exact lt_of_lt_of_le hheavy (support_mul_xMon_degree S _ s hsS)

end AC02Frege.P2MMajorityFoundation
end

section
-- Inlined Solutions.P2MBooleanBasis

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation

namespace AC02Frege.P2MBooleanBasis

theorem squarefree_eq_indicator {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s = Finsupp.indicator s.support (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i ∈ s.support
  · simp only [Finsupp.indicator_apply, dif_pos hi]
    have hpos := Finsupp.mem_support_iff.mp hi
    exact Nat.le_antisymm (hs i) (by omega)
  · simpa only [Finsupp.indicator_apply, dif_neg hi] using (by simpa only [Finsupp.mem_support_iff, not_not] using hi : s i = 0)

theorem squarefree_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2)
    (hs : ∀ i, s i ≤ 1) : monomial s c = c • xMon s.support := by
  rw [xMon_eq_monomial, smul_monomial, smul_eq_mul, mul_one,
    ← squarefree_eq_indicator s hs]

theorem squarefree_sum {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s.sum (fun _ e => e) = s.support.card := by
  have heq := squarefree_monomial s (1 : ZMod 2) hs
  have hd := congrArg MvPolynomial.totalDegree heq
  simpa only [totalDegree_monomial _ one_ne_zero, one_smul, xMon_totalDegree] using hd

noncomputable def monomialSpan {V : Type*} (P : Finset V → Prop) :
    Submodule (ZMod 2) (MvPolynomial V (ZMod 2)) :=
  Submodule.span (ZMod 2) {p | ∃ S : Finset V, P S ∧ p = xMon S}

theorem mem_monomialSpan_iff {V : Type*} (P : Finset V → Prop)
    (p : MvPolynomial V (ZMod 2)) : p ∈ monomialSpan P ↔
      IsMultilinear p ∧ ∀ s ∈ p.support, P s.support := by
  classical
  let M := restrictSupport (ZMod 2) {s : V →₀ ℕ | (∀ i, s i ≤ 1) ∧ P s.support}
  have heq : monomialSpan P = M := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro q ⟨S, hS, rfl⟩
      rw [xMon_eq_monomial]
      apply (monomial_mem_restrictSupport (ZMod 2)).mpr
      left
      refine ⟨?_, ?_⟩
      · intro i
        simp only [Finsupp.indicator_apply]
        split_ifs <;> omega
      · simpa only [indicator_support] using hS
    · intro q hq
      have hq' : ∀ s ∈ q.support, (∀ i, s i ≤ 1) ∧ P s.support := hq
      rw [q.as_sum]
      apply Submodule.sum_mem
      intro s hs
      obtain ⟨hml, hP⟩ := hq' s hs
      rw [squarefree_monomial s _ hml]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s.support, hP, rfl⟩)
  rw [heq, mem_restrictSupport_iff (ZMod 2)]
  constructor
  · intro hp
    exact ⟨fun s hs i => (hp hs).1 i, fun s hs => (hp hs).2⟩
  · rintro ⟨hml, hP⟩ s hs
    exact ⟨hml s hs, hP s hs⟩

theorem mem_light_iff {V : Type*} (m : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ monomialSpan (fun S : Finset V => S.card ≤ m) ↔
      IsMultilinear p ∧ p.totalDegree ≤ m := by
  rw [mem_monomialSpan_iff]
  constructor
  · rintro ⟨hp, hP⟩
    refine ⟨hp, Finset.sup_le fun s hs => ?_⟩
    rw [squarefree_sum s (hp s hs)]
    exact hP s hs
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun s hs => ?_⟩
    rw [← squarefree_sum s (hp s hs)]
    exact (le_totalDegree hs).trans hd

theorem point_interpolation {V : Type} [Fintype V] [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) :
    p = ∑ S : Finset V, eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p • pointPoly S := by
  apply multilinear_ext hp
    (multilinear_sum _ _ (fun S _ =>
      (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).smul_mem _
        ((mem_restrictDegree V _ 1).mpr (pointPoly_multilinear S)))))
  intro x
  simp only [map_sum, smul_eval, pointPoly_eval]
  have heq (S : Finset V) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro h; rw [h, ones_of_point]
    · intro h; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp
  have hx : (fun i => if x i = 1 then (1 : ZMod 2) else 0) = x := by
    funext i
    rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]
  rw [hx]

end AC02Frege.P2MBooleanBasis
end

section
-- Inlined Solutions.P2MExpansionNormalFormFixed

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionNormalFormFixed

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

noncomputable def normalSpan {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  Submodule.span (ZMod 2) (xMon '' {t | IsIrred m G t})

theorem normal_multilinear {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) (hp : p∈normalSpan m G) : IsMultilinear p := by
  apply (mem_restrictDegree σ p 1).mp
  apply (show normalSpan m G ≤ restrictDegree σ (ZMod 2) 1 from ?_) hp
  apply Submodule.span_le.mpr
  rintro q ⟨t,ht,rfl⟩
  exact (mem_restrictDegree σ _ 1).mpr (xMon_multilinear t)

theorem supported {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2))) :
    normalSpan m G ≤ restrictSupport (ZMod 2)
      {d | ∀ q∈idealB G, q≠0 → m.degree q≠d} := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,rfl⟩
  rw [xMon_eq_monomial]
  apply (monomial_mem_restrictSupport (ZMod 2)).mpr
  left
  intro q hq hn
  have hh := ht q hq hn
  simpa only [xMon_eq_monomial,m.degree_monomial,if_neg one_ne_zero] using hh

theorem zero_of_ideal {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) (hp : p∈normalSpan m G)
    (hI : p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) : p=0 := by
  by_contra hn
  have hstd := supported m G hp
  exact (hstd (m.degree_mem_support hn)) p ⟨normal_multilinear m G p hp,hI⟩ hn rfl

theorem nf_fixed {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (t : Finset σ) (ht : IsIrred m G t) : nf m G (xMon t)=xMon t := by
  have hp : xMon t∈normalSpan m G := Submodule.subset_span ⟨t,ht,rfl⟩
  have hex : ∃ q∈normalSpan m G,
      xMon t-q∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := ⟨xMon t,hp,by simp⟩
  have hchoice : nf m G (xMon t)∈normalSpan m G ∧
      xMon t-nf m G (xMon t)∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by
    unfold normalSpan at hex
    simp only [nf,dif_pos hex,normalSpan]
    exact hex.choose_spec
  exact (sub_eq_zero.mp (zero_of_ideal m G _ ((normalSpan m G).sub_mem hp hchoice.1) hchoice.2)).symm

theorem expOp_fixed {σ L R : Type} [DecidableEq σ] [Fintype L] [DecidableEq L] [Fintype R]
    [DecidableEq R] (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (t : Finset σ)
    (ht : IsIrred m P.F0 t) (hSup : supS P.graph s (t.image P.cluster)=∅) : expOp P m s t=xMon t := by
  unfold expOp
  rw [hSup]
  have he : P.F0 ∪ {p | ∃ u∈(∅ : Finset L), p∈P.Fu u}=P.F0 := by ext p; simp
  rw [he]
  exact nf_fixed m P.F0 t ht

end SemAC02.Supplement.P2MExpansionNormalFormFixed
end

section
-- Inlined Solutions.P2MExpansionFixedMonomialRank

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionFixedMonomialRank

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MExpansionNormalFormFixed

theorem count {σ L R : Type} [Fintype σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (k : ℕ)
    (E : Finset (Finset σ))
    (hstd : ∀ t∈E, IsIrred m P.F0 t) (hdeg : ∀ t∈E, t.card ≤ k)
    (hSup : ∀ t∈E, supS P.graph s (t.image P.cluster)=∅) : E.card ≤ expRank P m s k := by
  let U := Submodule.span (ZMod 2) (expOp P m s '' {t | IsIrred m P.F0 t ∧ t.card ≤ k})
  have hfinite : (expOp P m s '' {t | IsIrred m P.F0 t ∧ t.card ≤ k}).Finite :=
    (Set.toFinite _).image _
  letI : Module.Finite (ZMod 2) U := Module.Finite.span_of_finite (ZMod 2) hfinite
  have hmem (t : E) : xMon t.1∈U := by
    rw [←expOp_fixed P m s t.1 (hstd t.1 t.2) (hSup t.1 t.2)]
    exact Submodule.subset_span ⟨t.1,⟨hstd t.1 t.2,hdeg t.1 t.2⟩,rfl⟩
  let b (t : E) : U := ⟨xMon t.1,hmem t⟩
  have hb : LinearIndependent (ZMod 2) b := by
    apply LinearIndependent.of_comp U.subtype
    exact xMon_linearIndependent.comp Subtype.val Subtype.val_injective
  simpa only [Fintype.card_coe,U,expRank] using hb.fintype_card_le_finrank

end SemAC02.Supplement.P2MExpansionFixedMonomialRank
end

section
-- Inlined Solutions.P2MClusterMonomialChoices

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MClusterMonomialChoices

variable {σ R : Type} [Fintype σ] [DecidableEq σ] [Fintype R] [DecidableEq R]

abbrev Choice (cl : σ → R) (A : Finset R) := (v : A) → {x : σ // cl x=v.1}

noncomputable def selected (cl : σ → R) (A : Finset R) (a : Choice cl A) : Finset σ :=
  Finset.univ.image (fun v : A => (a v).1)

lemma selected_injective (cl : σ → R) (A : Finset R) (a : Choice cl A) :
    Function.Injective (fun v : A => (a v).1) := by
  intro v w he
  apply Subtype.ext
  exact (a v).2.symm.trans ((congrArg cl he).trans (a w).2)

theorem selected_card (cl : σ → R) (A : Finset R) (a : Choice cl A) : (selected cl A a).card=A.card := by
  rw [selected,Finset.card_image_of_injective _ (selected_injective cl A a),Finset.card_univ,Fintype.card_coe]

theorem selected_image (cl : σ → R) (A : Finset R) (a : Choice cl A) : (selected cl A a).image cl=A := by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
    rw [(a w).2]
    exact w.2
  · intro hv
    refine Finset.mem_image.mpr ⟨(a ⟨v,hv⟩).1,?_,(a ⟨v,hv⟩).2⟩
    exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩

theorem one_per_cluster (cl : σ → R) (A : Finset R) (a : Choice cl A) :
    ∀ x∈selected cl A a, ∀ y∈selected cl A a, cl x=cl y → x=y := by
  intro x hx y hy he
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
  have he' : v=w := Subtype.ext ((a v).2.symm.trans (he.trans (a w).2))
  rw [he']

theorem selected_determines_choice (cl : σ → R) (A : Finset R) (a b : Choice cl A)
    (he : selected cl A a=selected cl A b) : a=b := by
  funext v
  apply Subtype.ext
  have hx : (a v).1∈selected cl A b := by
    rw [←he]
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  obtain ⟨w,hw,hwe⟩ := Finset.mem_image.mp hx
  have he' : w=v := Subtype.ext ((b w).2.symm.trans ((congrArg cl hwe).trans (a v).2))
  subst w
  exact hwe.symm

theorem choice_card (cl : σ → R) (D : ℕ)
    (hcl : ∀ v : R, (Finset.univ.filter (fun x => cl x=v)).card=D) (A : Finset R) :
    Fintype.card (Choice cl A)=D^A.card := by
  classical
  rw [Fintype.card_pi]
  have hf (v : A) : Fintype.card {x : σ // cl x=v.1}=D := by
    rw [Fintype.card_subtype]
    exact hcl v.1
  simp only [hf,Finset.prod_const,Finset.card_univ,Fintype.card_coe]

theorem sigma_selected_injective (cl : σ → R) (E : Finset (Finset R)) :
    Function.Injective (fun z : (A : E) × Choice cl A.1 => selected cl z.1.1 z.2) := by
  intro z w he
  rcases z with ⟨A,a⟩
  rcases w with ⟨B,b⟩
  have hAB : A=B := Subtype.ext (by
    have hi := congrArg (Finset.image cl) he
    simpa only [selected_image] using hi)
  subst B
  have hab : a=b := selected_determines_choice cl A.1 a b he
  subst b
  rfl

end P2MProofComplexity.P2MClusterMonomialChoices
end

section
-- Inlined Solutions.P2MExpansionAvoidingRank

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionAvoidingRank

open AC02Frege P2MProofComplexity.P2MClusterMonomialChoices P2MBoundaryAvoidance

theorem count {σ L R : Type} [Fintype σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (k D : ℕ)
    (hcl : ∀ v : R, (Finset.univ.filter (fun x => P.cluster x=v)).card=D)
    (hirr : ∀ t : Finset σ, (∀ x∈t, ∀ y∈t, P.cluster x=P.cluster y → x=y) → IsIrred m P.F0 t)
    (E : Finset (Finset R)) (hk : ∀ A∈E, A.card=k) (hA : ∀ A∈E, Avoiding P.graph s A) :
    E.card*D^k ≤ expRank P m s k := by
  let I := (Σ A : E, Choice P.cluster A.1)
  let f (z : I) : Finset σ := selected P.cluster z.1.1 z.2
  let T : Finset (Finset σ) := Finset.univ.image f
  have hcount : T.card=E.card*D^k := by
    rw [Finset.card_image_of_injective _ (sigma_selected_injective P.cluster E),Finset.card_univ]
    change Fintype.card (Σ A : E, Choice P.cluster A.1)=E.card*D^k
    rw [Fintype.card_sigma]
    have he (A : E) : Fintype.card (Choice P.cluster A.1)=D^k := by
      rw [choice_card P.cluster D hcl,hk A.1 A.2]
    simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul]
  rw [←hcount]
  apply P2MExpansionFixedMonomialRank.count P m s k T
  · intro t ht
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
    exact hirr _ (one_per_cluster P.cluster z.1.1 z.2)
  · intro t ht
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
    change (selected P.cluster z.1.1 z.2).card ≤ k
    rw [selected_card,hk z.1.1 z.1.2]
  · intro t ht
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
    change supS P.graph s ((selected P.cluster z.1.1 z.2).image P.cluster)=∅
    rw [selected_image]
    exact sup_eq_empty P.graph s z.1.1 (hA z.1.1 z.1.2)

end SemAC02.Supplement.P2MExpansionAvoidingRank
end

section
-- Inlined Solutions.P2MBooleanLocality

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MBooleanLocality

theorem multilinear_degree_le_card {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) : p.totalDegree ≤ Fintype.card V := by
  classical
  apply Finset.sup_le
  intro s hs
  rw [squarefree_sum s (hp s hs)]
  exact Finset.card_le_univ _

noncomputable def extendAssignment {V : Type} (J : Finset V) (x : J → ZMod 2) : V → Bool := by
  classical
  exact fun i => if hi : i ∈ J then decide (x ⟨i, hi⟩ = 1) else false

theorem represents_local_function {V : Type} [Fintype V] (J : Finset V)
    (f : (V → Bool) → ZMod 2)
    (hf : ∀ z z' : V → Bool, (∀ i ∈ J, z i = z' i) → f z = f z') :
    ∃ r : MvPolynomial V (ZMod 2), r.totalDegree ≤ J.card ∧
      ∀ z : V → Bool, eval (toF2 z) r = f z := by
  classical
  let η : (J → ZMod 2) → ZMod 2 := fun x => f (extendAssignment J x)
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ J (ZMod 2)) η
  let p' : restrictDegree J (ZMod 2) (Fintype.card (ZMod 2) - 1) := p
  have hml : IsMultilinear p'.1 := by
    apply (mem_restrictDegree J _ 1).mp
    simpa only [ZMod.card, Nat.reduceSub] using p'.2
  refine ⟨rename Subtype.val p'.1, ?_, ?_⟩
  · apply (totalDegree_rename_le _ _).trans
    simpa only [Fintype.card_coe] using multilinear_degree_le_card p'.1 hml
  · intro z
    rw [eval_rename]
    have he := congrFun hp (fun j : J => toF2 z j.1)
    change eval (fun j : J => toF2 z j.1) p'.1 = f (extendAssignment J (fun j : J => toF2 z j.1)) at he
    change eval (fun j : J => toF2 z j.1) p'.1 = f z
    rw [he]
    apply hf
    intro i hi
    simp only [extendAssignment, dif_pos hi]
    cases h : z i <;> simp [toF2, h]

end SemAC02.P2MBooleanLocality
end

section
-- Inlined Solutions.P2MBooleanFlip

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation AC02Frege.P2MBooleanBasis

namespace AC02Frege.P2MBooleanFlip

theorem ml_totalDegree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (ML p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_monomial_le _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  simp only [Finsupp.sum, sqfree_support]
  apply Finset.sum_le_sum
  intro i _
  simp only [sqfree, Finsupp.mapRange_apply]
  exact min_le_left _ _

theorem bind_linear_totalDegree_le {V W : Type*} (f : V → MvPolynomial W (ZMod 2))
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial V (ZMod 2)) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, bind₁_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

noncomputable def flip {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    MvPolynomial V (ZMod 2) := ML (bind₁ (fun i => 1 + X i) p)

theorem flip_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (flip p) := ml_multilinear _

theorem flip_degree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (flip p).totalDegree ≤ p.totalDegree := by
  apply (ml_totalDegree_le _).trans
  apply bind_linear_totalDegree_le
  intro i
  exact (totalDegree_add _ _).trans (by simp)

theorem flip_eval {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (flip p) = eval (fun i => 1 + x i) p := by
  rw [flip, eval_ml]
  simp only [eval, eval₂Hom_bind₁, map_add, map_one, eval₂Hom_X']

theorem flip_involution {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : flip (flip p) = p := by
  apply multilinear_ext (flip_multilinear _) hp
  intro x
  simp only [flip_eval, CharTwo.add_cancel_left]

end AC02Frege.P2MBooleanFlip
end

section
-- Inlined Solutions.P2MBooleanRestrictions

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation
open AC02Frege.P2MBooleanBasis AC02Frege.P2MBooleanFlip

namespace AC02Frege.P2MBooleanRestrictions

theorem xMon_eval_point {V : Type*} [DecidableEq V] (S T : Finset V) :
    eval (fun i => if i ∈ T then (1 : ZMod 2) else 0) (xMon S) =
      if S ⊆ T then 1 else 0 := by
  classical
  rw [xMon_eval]
  by_cases h : S ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by simp [hit])

theorem multilinear_exponent_ext {V : Type*} (s t : V →₀ ℕ)
    (hs : ∀ i, s i ≤ 1) (ht : ∀ i, t i ≤ 1) (hst : s.support = t.support) : s = t := by
  rw [squarefree_eq_indicator s hs, squarefree_eq_indicator t ht, hst]

theorem eq_zero_of_support_point_eval_zero {V : Type} [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (hv : ∀ s ∈ p.support,
      eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  classical
  by_contra hne
  obtain ⟨s, hs, hmin⟩ := p.support.exists_min_image
    (fun t => t.support.card) (support_nonempty.mpr hne)
  have heval : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = p.coeff s := by
    have hsum : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p =
        ∑ t ∈ p.support, p.coeff t * (if t.support ⊆ s.support then (1 : ZMod 2) else 0) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [squarefree_monomial t _ (hp t ht), smul_eval, xMon_eval_point]
    rw [hsum, Finset.sum_eq_single s]
    · simp
    · intro t ht hts
      have hnot : ¬ t.support ⊆ s.support := by
        intro hsub
        have heq : t.support = s.support := Finset.eq_of_subset_of_card_le hsub (hmin t ht)
        exact hts (multilinear_exponent_ext t s (hp t ht) (hp s hs) heq)
      rw [if_neg hnot, mul_zero]
    · intro hnot
      exact False.elim (hnot hs)
  have hz := hv s hs
  rw [heval] at hz
  exact (mem_support_iff.mp hs) hz

theorem eval_injective_on_monomialSpan {V : Type} [DecidableEq V]
    (P : Finset V → Prop) (p : MvPolynomial V (ZMod 2))
    (hp : p ∈ monomialSpan P)
    (hv : ∀ S : Finset V, P S →
      eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  obtain ⟨hml, hP⟩ := (mem_monomialSpan_iff P p).mp hp
  exact eq_zero_of_support_point_eval_zero p hml (fun s hs => hv s.support (hP s hs))

theorem ml_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (ML p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨s, hs, his⟩ := (mem_vars_iff_mem_support i).mp hi
  have hexp : ML p = ∑ t ∈ p.support, monomial (sqfree t) (p.coeff t) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, ml_monomial]
  rw [hexp] at hs
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have heq := Finset.mem_singleton.mp (support_monomial_subset hst)
  subst s
  rw [sqfree_support] at his
  exact (mem_vars_iff_mem_support i).mpr ⟨t, ht, his⟩

theorem flip_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (P2MBooleanFlip.flip p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp
    (vars_bind₁ (fun j => 1 + X j) p (ml_vars_subset _ hi))
  have hsub : (1 + X j : MvPolynomial V (ZMod 2)).vars ⊆ {j} := by
    simpa using vars_add_subset (1 : MvPolynomial V (ZMod 2)) (X j)
  have heq := Finset.mem_singleton.mp (hsub hij)
  simpa only [heq] using hj

noncomputable def complementMap {V : Type} :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) where
  toFun := P2MBooleanFlip.flip
  map_add' p q := by simp only [P2MBooleanFlip.flip, map_add]
  map_smul' c p := by simp only [P2MBooleanFlip.flip, map_smul, RingHom.id_apply]

theorem flip_mem_monomialSpan {V : Type} (P : Finset V → Prop)
    (hP : ∀ S T, T ⊆ S → P S → P T)
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ monomialSpan P) :
    P2MBooleanFlip.flip p ∈ monomialSpan P := by
  classical
  have hle : monomialSpan P ≤ (monomialSpan P).comap complementMap := by
    apply Submodule.span_le.mpr
    rintro q ⟨S, hS, rfl⟩
    apply (mem_monomialSpan_iff P _).mpr
    refine ⟨flip_multilinear _, ?_⟩
    intro s hs
    have hsub : s.support ⊆ S := by
      apply (support_subset_vars_of_mem_support hs).trans
      apply (flip_vars_subset _).trans
      rw [xMon_eq_monomial, vars_monomial one_ne_zero, indicator_support]
    exact hP S s.support hsub hS
  exact hle hp

theorem monomialSpan_span_range {V : Type} (P : Finset V → Prop) :
    monomialSpan P = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset V // P S} => xMon S.1)) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨⟨S, hS⟩, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S.1, S.2, rfl⟩

end AC02Frege.P2MBooleanRestrictions
end

section
-- Inlined Solutions.P2MCommonBasis

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation
open AC02Frege.P2MBooleanBasis AC02Frege.P2MBooleanFlip AC02Frege.P2MBooleanRestrictions

namespace SemAC02.P2MCommonBasis

def ones {m : ℕ} (X : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => X i = true)

theorem indicator_ones {m : ℕ} (X : Fin m → Bool) : indicatorVec (ones X) = X := by
  funext i
  cases h : X i <;> simp [indicatorVec, ones, h]

theorem ones_indicator {m : ℕ} (S : Finset (Fin m)) : ones (indicatorVec S) = S := by
  ext i
  simp [indicatorVec, ones]

theorem toF2_indicator {m : ℕ} (S : Finset (Fin m)) :
    toF2 (indicatorVec S) = fun i => if i ∈ S then (1 : ZMod 2) else 0 := by
  funext i
  simp [toF2, indicatorVec]

theorem flip_eval_bool {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2)) (X : Fin m → Bool) :
    eval (toF2 X) (P2MBooleanFlip.flip p) = eval (toF2 (fun i => !X i)) p := by
  rw [flip_eval]
  have heq : (fun i => 1 + toF2 X i) = toF2 (fun i => !X i) := by
    funext i
    cases h : X i <;> simp [toF2, h, CharTwo.add_self_eq_zero]
  rw [heq]

noncomputable def supportEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {S : Finset (Fin m) // g (indicatorVec S) = true} ≃
      {X : Fin m → Bool // g X = true} where
  toFun S := ⟨indicatorVec S.1, S.2⟩
  invFun X := ⟨ones X.1, by simpa only [indicator_ones] using X.2⟩
  left_inv S := Subtype.ext (ones_indicator S.1)
  right_inv X := Subtype.ext (indicator_ones X.1)

def complementEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {X : Fin m → Bool // g X = true} ≃
      {X : Fin m → Bool // g (fun i => !X i) = true} where
  toFun X := ⟨fun i => !X.1 i, by simpa only [Bool.not_not] using X.2⟩
  invFun X := ⟨fun i => !X.1 i, X.2⟩
  left_inv X := Subtype.ext (by funext i; simp)
  right_inv X := Subtype.ext (by funext i; simp)

noncomputable def restriction {m : ℕ} (Ω : Set (Fin m → Bool)) :
    MvPolynomial (Fin m) (ZMod 2) →ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun p X := eval (toF2 X.1) p
  map_add' p q := by ext X; simp
  map_smul' c p := by ext X; simp

theorem downclosed {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) :
    ∀ S T : Finset (Fin m), T ⊆ S → g (indicatorVec S) = true →
      g (indicatorVec T) = true := by
  intro S T hTS hS
  have hle : indicatorVec T ≤ indicatorVec S := by
    intro i
    by_cases hi : i ∈ T
    · simp [indicatorVec, hi, hTS hi]
    · simp [indicatorVec, hi]
  have h := hg hle
  rw [hS] at h
  exact Bool.eq_true_of_true_le h

theorem restriction_zero (m : ℕ) (g : (Fin m → Bool) → Bool)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g X = true} p = 0) : p = 0 := by
  apply eval_injective_on_monomialSpan _ p hp
  intro S hS
  have h := congrFun hv ⟨indicatorVec S, hS⟩
  change eval (toF2 (indicatorVec S)) p = 0 at h
  simpa only [toF2_indicator] using h

theorem restriction_complement_zero (m : ℕ) (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g (fun i => !X i) = true} p = 0) : p = 0 := by
  have hf : P2MBooleanFlip.flip p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true) :=
    flip_mem_monomialSpan _ (downclosed g hg) p hp
  have hvan : restriction {X : Fin m → Bool | g X = true} (P2MBooleanFlip.flip p) = 0 := by
    funext X
    change eval (toF2 X.1) (P2MBooleanFlip.flip p) = 0
    rw [flip_eval_bool]
    have h := congrFun hv ⟨fun i => !X.1 i, by simpa only [Set.mem_ofPred_eq, Bool.not_not] using X.2⟩
    exact h
  have hz := restriction_zero m g _ hf hvan
  have hml := ((mem_monomialSpan_iff _ _).mp hp).1
  calc
    p = P2MBooleanFlip.flip (P2MBooleanFlip.flip p) := (flip_involution p hml).symm
    _ = P2MBooleanFlip.flip 0 := congrArg (P2MBooleanFlip.flip (V := Fin m)) hz
    _ = 0 := by simp [P2MBooleanFlip.flip]

theorem restriction_independent (m : ℕ) (P : Finset (Fin m) → Prop) (Ω : Set (Fin m → Bool))
    (hinj : ∀ p : MvPolynomial (Fin m) (ZMod 2), p ∈ monomialSpan P → restriction Ω p = 0 → p = 0) :
    LinearIndependent (ZMod 2) (fun S : {S : Finset (Fin m) // P S} => restriction Ω (xMon S.1)) := by
  apply (xMon_linearIndependent.comp Subtype.val Subtype.val_injective).map_injOn
  intro v hv w hw heq
  have hv' : v ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  have hw' : w ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  apply sub_eq_zero.mp
  apply hinj (v - w) (Submodule.sub_mem _ hv' hw')
  rw [map_sub, heq, sub_self]

end SemAC02.P2MCommonBasis
end

section
-- Inlined Theorems.Thm_SemAC02_lemma_8_5_common_basis


open MvPolynomial AC02Frege SemAC02 SemAC02.P2MCommonBasis


/-- **Lemma 8.5 (Common monomial basis)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.5, p.64): with
`L = {S ⊆ [m] : g₀(1_S) = 1}`, `Ω₀ = {X : g₀(X) = 1}` and `Ω₁ = {X : g₁(X) = 1}`,
`g₁(X) = g₀(X̄)`, the monomials `x_S = ∏_{j∈S} x_j`, `S ∈ L`, give a basis of both `𝔽₂^{Ω₀}`
and `𝔽₂^{Ω₁}`.

**Formalization Note** Stated for every antitone Boolean function `g₀` on `{0,1}^m` (the
paper's `g₀ = g` from §8.1 is one). "Basis" is linear independence of the restrictions of the
`x_S` to `Ω_b` together with spanning all functions `Ω_b → 𝔽₂`. -/
theorem SemAC02.lemma_8_5_common_basis {m : ℕ} (g₀ : (Fin m → Bool) → Bool) (hg₀ : Antitone g₀) :
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) ∧
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) := by
  classical
  let P : Finset (Fin m) → Prop := fun S => g₀ (indicatorVec S) = true
  let Ω₀ : Set (Fin m → Bool) := {X | g₀ X = true}
  let Ω₁ : Set (Fin m → Bool) := {X | g₀ (fun i => !X i) = true}
  have hli0 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₀ (xMon S.1)) :=
    restriction_independent m P Ω₀ (restriction_zero m g₀)
  have hli1 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₁ (xMon S.1)) :=
    restriction_independent m P Ω₁ (restriction_complement_zero m g₀ hg₀)
  have hspan0 := hli0.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr (supportEquiv m g₀))
  have hspan1 := hli1.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr ((supportEquiv m g₀).trans (complementEquiv m g₀)))
  exact ⟨⟨hli0, hspan0⟩, ⟨hli1, hspan1⟩⟩

end

section
-- Inlined Solutions.ProductFunctionBasis

open Module
open scoped TensorProduct

namespace P2MProofComplexity

open PiTensorProduct

noncomputable def functionTensorEquiv
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] :
    (⨂[R] i, (X i → R)) ≃ₗ[R] (((i : ι) → X i) → R) := by
  classical
  exact (PiTensorProduct.congr (fun i => (Finsupp.linearEquivFunOnFinite R R (X i)).symm)) ≪≫ₗ
    (PiTensorProduct.ofFinsuppEquiv' (R := R) (κ := X)) ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R R ((i : ι) → X i)

@[simp] theorem functionTensorEquiv_tprod
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] (f : (i : ι) → X i → R) (x : (i : ι) → X i) :
    functionTensorEquiv X (⨂ₜ[R] i, f i) x = ∏ i, f i (x i) := by
  classical
  simp [functionTensorEquiv]

noncomputable def productFunctionBasis
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) :
    Basis ((i : ι) → κ i) R (((i : ι) → X i) → R) :=
  (Basis.piTensorProduct b).map (functionTensorEquiv X)

@[simp] theorem productFunctionBasis_apply
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (k : (i : ι) → κ i) (x : (i : ι) → X i) :
    productFunctionBasis b k x = ∏ i, b i (k i) (x i) := by
  classical
  simp [productFunctionBasis]

theorem productFunctionBasis_repr
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (f : (i : ι) → X i → R)
    (k : (i : ι) → κ i) :
    (productFunctionBasis b).repr (fun x => ∏ i, f i (x i)) k =
      ∏ i, (b i).repr (f i) (k i) := by
  classical
  have hfun : (fun x => ∏ i, f i (x i)) = functionTensorEquiv X (⨂ₜ[R] i, f i) := by
    funext x
    exact (functionTensorEquiv_tprod X f x).symm
  rw [hfun]
  change (Basis.piTensorProduct b).repr
    ((functionTensorEquiv X).symm (functionTensorEquiv X (⨂ₜ[R] i, f i))) k = _
  rw [LinearEquiv.symm_apply_apply]
  exact Basis.piTensorProduct_repr_tprod_apply b f k

end P2MProofComplexity
end

section
-- Inlined Solutions.SemanticFibreBasis

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MFibreBasis

abbrev BlockIndex {m : ℕ} (g : (Fin m → Bool) → Bool) :=
  {S : Finset (Fin m) // g (indicatorVec S) = true}

abbrev BlockFibre {m : ℕ} (g : (Fin m → Bool) → Bool) (b : Bool) :=
  {X : Fin m → Bool // if b then g (fun j => !X j) = true else g X = true}

noncomputable def blockBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) (b : Bool) :
    Basis (BlockIndex g) (ZMod 2) (BlockFibre g b → ZMod 2) := by
  have h := lemma_8_5_common_basis g hg
  cases b with
  | false => exact Basis.mk h.1.1 h.1.2.ge
  | true => exact Basis.mk h.2.1 h.2.2.ge

@[simp] theorem blockBasis_apply {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (b : Bool) (S : BlockIndex g) (X : BlockFibre g b) :
    blockBasis g hg b S X = eval (toF2 X.1) (xMon S.1) := by
  cases b <;> simp [blockBasis, Basis.mk_apply]

abbrev GlobalIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n : ℕ) :=
  {A : Finset (Fin n × Fin m) // IsLnSupport g A}

def assemble {n m : ℕ} {g : (Fin m → Bool) → Bool} (S : Fin n → BlockIndex g) :
    Finset (Fin n × Fin m) := Finset.univ.filter (fun v => v.2 ∈ (S v.1).1)

@[simp] theorem section_assemble {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (S : Fin n → BlockIndex g) (i : Fin n) : blockSection (assemble S) i = (S i).1 := by
  ext j
  simp [blockSection, assemble]

def sections {n m : ℕ} {g : (Fin m → Bool) → Bool} (A : GlobalIndex g n) (i : Fin n) :
    BlockIndex g := ⟨blockSection A.1 i, A.2 i⟩

@[simp] theorem assemble_sections {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (A : GlobalIndex g n) : assemble (sections A) = A.1 := by
  ext v
  simp [assemble, sections, blockSection]

def indexEquiv (n : ℕ) {m : ℕ} (g : (Fin m → Bool) → Bool) :
    (Fin n → BlockIndex g) ≃ GlobalIndex g n where
  toFun S := ⟨assemble S, by
    intro i
    rw [section_assemble]
    exact (S i).2⟩
  invFun A := sections A
  left_inv S := by funext i; apply Subtype.ext; exact section_assemble S i
  right_inv A := Subtype.ext (assemble_sections A)

abbrev Fibre {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :=
  {X : Fin n × Fin m → Bool // InFiber g z X}

def curryEquiv {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :
    Fibre g z ≃ ((i : Fin n) → BlockFibre g (z i)) where
  toFun X i := ⟨fun j => X.1 (i, j), X.2 i⟩
  invFun X := ⟨fun v => (X v.1).1 v.2, fun i => (X i).2⟩
  left_inv X := Subtype.ext (by funext v; rfl)
  right_inv X := by funext i; apply Subtype.ext; rfl

noncomputable def fibreBasis {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) : Basis (GlobalIndex g n) (ZMod 2) (Fibre g z → ZMod 2) :=
  ((P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).reindex
    (indexEquiv n g)).map (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))

theorem xMon_eval_blocks {n m : ℕ} (A : Finset (Fin n × Fin m))
    (X : Fin n × Fin m → Bool) : eval (toF2 X) (xMon A) =
      ∏ i : Fin n, eval (toF2 (fun j => X (i, j))) (xMon (blockSection A i)) := by
  classical
  simp only [xMon_eval, blockSection, Finset.prod_filter, toF2]
  rw [← Finset.prod_product']
  simp only [Finset.univ_product_univ]
  rw [← Finset.prod_filter]
  simp

@[simp] theorem fibreBasis_apply {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) (A : GlobalIndex g n) (X : Fibre g z) :
    fibreBasis g hg z A X = eval (toF2 X.1) (xMon A.1) := by
  classical
  rw [fibreBasis, Basis.map_apply, Basis.reindex_apply]
  change P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))
    (sections A) (curryEquiv g z X) = _
  rw [P2MProofComplexity.productFunctionBasis_apply, xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [blockBasis_apply]
  rfl

end SemAC02.P2MFibreBasis
end

section
-- Inlined Solutions.SemanticFibreCoordinates

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis

namespace SemAC02.P2MFibreCoordinates

noncomputable def coordinates {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) : ZMod 2 :=
  (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) p) S

theorem coordinates_expansion {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) (X : Fibre g z) :
    eval (toF2 X.1) p = ∑ S : GlobalIndex g n, coordinates g hg p S z *
      eval (toF2 X.1) (xMon S.1) := by
  classical
  have h := congrFun ((fibreBasis g hg z).equivFun.symm_apply_apply (fun X => eval (toF2 X.1) p)) X
  rw [Basis.equivFun_symm_apply] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply, coordinates] using h.symm

theorem coordinates_unique {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (c : GlobalIndex g n → (Fin n → Bool) → ZMod 2)
    (hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin m → Bool), InFiber g z X →
      eval (toF2 X) p = ∑ S, c S z * eval (toF2 X) (xMon S.1)) :
    ∀ S z, c S z = coordinates g hg p S z := by
  classical
  intro S z
  have he : (fun X : Fibre g z => eval (toF2 X.1) p) =
      (fibreBasis g hg z).equivFun.symm (fun S => c S z) := by
    rw [Basis.equivFun_symm_apply]
    funext X
    rw [hc z X.1 X.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply]
  have h := congrArg (fibreBasis g hg z).equivFun he
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrFun h S).symm

theorem coordinates_add {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p q : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p + q) S z = coordinates g hg p S z + coordinates g hg q S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p + q)) =
      (fun X => eval (toF2 X.1) p) + (fun X => eval (toF2 X.1) q) := by
    funext X
    exact map_add _ _ _
  unfold coordinates
  rw [he, map_add]
  rfl

theorem coordinates_smul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (a : ZMod 2) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (a • p) S z = a * coordinates g hg p S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (a • p)) =
      a • (fun X => eval (toF2 X.1) p) := by
    funext X
    simp only [smul_eval, Pi.smul_apply, smul_eq_mul]
  unfold coordinates
  rw [he, map_smul]
  rfl

end SemAC02.P2MFibreCoordinates
end

section
-- Inlined Solutions.SemanticProductCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates

namespace SemAC02.P2MProductCoordinates

noncomputable def blockCoefficient {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (U : Finset (Fin m)) (b : Bool) : ZMod 2 :=
  (blockBasis g hg b).repr (fun X => eval (toF2 X.1) (xMon T.1 * xMon U)) S

theorem blockCoefficient_empty {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (b : Bool) :
    blockCoefficient g hg S T ∅ b = if S = T then 1 else 0 := by
  classical
  have he : (fun X : BlockFibre g b => eval (toF2 X.1) (xMon T.1 * xMon ∅)) =
      blockBasis g hg b T := by
    funext X
    simp only [xMon, Finset.prod_empty, mul_one, blockBasis_apply]
  unfold blockCoefficient
  rw [he, Basis.repr_self]
  by_cases hST : S = T
  · subst S
    rw [Finsupp.single_eq_same, if_pos rfl]
  · rw [Finsupp.single_eq_of_ne hST, if_neg hST]

theorem coordinates_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) (z : Fin n → Bool) :
    coordinates g hg (xMon T.1 * xMon U) S z =
      ∏ i : Fin n, blockCoefficient g hg (sections S i) (sections T i) (blockSection U i) (z i) := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon U)) =
      (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))
        (fun X : (i : Fin n) → BlockFibre g (z i) =>
          ∏ i : Fin n, eval (toF2 (X i).1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) := by
    funext X
    change eval (toF2 X.1) (xMon T.1 * xMon U) =
      ∏ i : Fin n, eval (toF2 (fun j => X.1 (i, j)))
        (xMon (blockSection T.1 i) * xMon (blockSection U i))
    simp only [map_mul, xMon_eval_blocks, Finset.prod_mul_distrib]
  unfold coordinates
  rw [he]
  change (P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).repr
    ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)).symm
      ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)) _)) ((indexEquiv n g).symm S) = _
  rw [LinearEquiv.symm_apply_apply]
  exact P2MProofComplexity.productFunctionBasis_repr (fun i : Fin n => blockBasis g hg (z i))
    (fun i X => eval (toF2 X.1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) (sections S)

theorem blockSection_empty {n m : ℕ} (U : Finset (Fin n × Fin m)) (i : Fin n)
    (hi : i ∉ U.image Prod.fst) : blockSection U i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply hi
  have hij : (i, j) ∈ U := (Finset.mem_filter.mp hj).2
  exact Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩

theorem coordinates_product_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m))
    (z z' : Fin n → Bool) (hz : ∀ i ∈ U.image Prod.fst, z i = z' i) :
    coordinates g hg (xMon T.1 * xMon U) S z = coordinates g hg (xMon T.1 * xMon U) S z' := by
  classical
  rw [coordinates_product, coordinates_product]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U.image Prod.fst
  · rw [hz i hi]
  · rw [blockSection_empty U i hi, blockCoefficient_empty, blockCoefficient_empty]

end SemAC02.P2MProductCoordinates
end

section
-- Inlined Solutions.SemanticCoordinateSpaces

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates

namespace SemAC02.P2MCoordinateSpaces

noncomputable def booleanEvaluation (n : ℕ) :
    MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p z := eval (toF2 z) p
  map_add' p q := by funext z; exact map_add _ _ _
  map_smul' a p := by funext z; simp only [smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

noncomputable def degreeSpace (n D : ℕ) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) :=
  (restrictTotalDegree (Fin n) (ZMod 2) D).map (booleanEvaluation n)

theorem mem_degreeSpace {n D : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    u ∈ degreeSpace n D ↔ ∃ r : MvPolynomial (Fin n) (ZMod 2), r.totalDegree ≤ D ∧
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  constructor
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mp hr, fun z => congrFun heq z⟩
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mpr hr, funext heq⟩

def localSpace {n : ℕ} (J : Finset (Fin n)) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) where
  carrier := {u | ∀ z z', (∀ i ∈ J, z i = z' i) → u z = u z'}
  zero_mem' := by intro z z' hz; rfl
  add_mem' := by intro f h hf hh z z' hz; exact congrArg₂ (· + ·) (hf z z' hz) (hh z z' hz)
  smul_mem' := by intro a f hf z z' hz; exact congrArg (fun x => a • x) (hf z z' hz)

theorem localSpace_mono {n : ℕ} {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    localSpace I ≤ localSpace J := by
  intro f hf z z' hz
  exact hf z z' (fun i hi => hz i (hIJ hi))

noncomputable def coordinateMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p := coordinates g hg p S
  map_add' p q := by funext z; exact coordinates_add g hg p q S z
  map_smul' a p := by
    funext z
    simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using coordinates_smul g hg a p S z

end SemAC02.P2MCoordinateSpaces
end

section
-- Inlined Solutions.P2MBooleanFunctionPolynomials

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MBooleanFunctionPolynomials

theorem toF2_surjective {V : Type} (x : V → ZMod 2) : ∃ X : V → Bool, toF2 X = x := by
  refine ⟨fun v => decide (x v = 1), ?_⟩
  funext v
  have h : x v = 0 ∨ x v = 1 := by
    have h01 := AC02Frege.P2MMajorityFoundation.eq_zero_or_one (x v)
    exact h01
  rcases h with h | h <;> simp [toF2, h]

theorem multilinear_ext_bool {V : Type} [Finite V] {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (he : ∀ X : V → Bool, eval (toF2 X) p = eval (toF2 X) q) : p = q := by
  apply multilinear_ext hp hq
  intro x
  obtain ⟨X, rfl⟩ := toF2_surjective x
  exact he X

theorem exists_polynomial (n : ℕ) (u : (Fin n → Bool) → ZMod 2) :
    ∃ r : MvPolynomial (Fin n) (ZMod 2),
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  classical
  obtain ⟨r, _, hr⟩ := P2MBooleanLocality.represents_local_function Finset.univ u
    (fun z z' h => congrArg u (funext (fun i => h i (Finset.mem_univ i))))
  exact ⟨r, hr⟩

noncomputable def polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    MvPolynomial (Fin n) (ZMod 2) := ML (Classical.choose (exists_polynomial n u))

theorem polynomial_multilinear {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    IsMultilinear (polynomial u) := ml_multilinear _

@[simp] theorem eval_polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) (z : Fin n → Bool) :
    eval (toF2 z) (polynomial u) = u z := by
  rw [polynomial, eval_ml]
  exact Classical.choose_spec (exists_polynomial n u) z

theorem polynomial_eq {n : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (r : MvPolynomial (Fin n) (ZMod 2))
    (hr : ∀ z : Fin n → Bool, eval (toF2 z) r = u z) : polynomial u = ML r := by
  apply multilinear_ext_bool
    (polynomial_multilinear u) (ml_multilinear r)
  intro z
  rw [eval_polynomial, eval_ml, hr]

noncomputable def polynomialMap (n : ℕ) :
    ((Fin n → Bool) → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) where
  toFun := polynomial
  map_add' u v := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.add_mem _ ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u))
          ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear v)))
    · intro z
      simp only [eval_polynomial, map_add, Pi.add_apply]
  map_smul' a u := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.smul_mem _ a ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u)))
    · intro z
      simp only [eval_polynomial, smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem polynomial_degree {n D : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (hu : u ∈ SemAC02.P2MCoordinateSpaces.degreeSpace n D) : (polynomial u).totalDegree ≤ D := by
  obtain ⟨r, hr, he⟩ := SemAC02.P2MCoordinateSpaces.mem_degreeSpace u |>.mp hu
  rw [polynomial_eq u r he]
  exact (ml_totalDegree_le r).trans hr

end SemAC02.P2MBooleanFunctionPolynomials
end

section
-- Inlined Solutions.P2MBooleanEmptyBackground

namespace SemAC02.Supplement.P2MBooleanEmptyBackground

open MvPolynomial AC02Frege

theorem ideal_zero {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2))
    (hp : p∈idealB ∅) : p=0 := by
  apply P2MBooleanFunctionPolynomials.multilinear_ext_bool hp.1 (by intro d hd; simp at hd)
  intro y
  have hker : Ideal.span ((∅ : Set (MvPolynomial V (ZMod 2))) ∪ {p | ∃ i : V, p=X i^2-X i}) ≤
      RingHom.ker (eval (toF2 y)) := by
    apply Ideal.span_le.mpr
    rintro q (hq | ⟨i,rfl⟩)
    · exact hq.elim
    · change eval (toF2 y) (X i^2-X i)=0
      cases hi : y i <;> simp [toF2,hi]
  have hh := hker hp.2
  change eval (toF2 y) p=0 at hh
  simpa only [map_zero] using hh

theorem irreducible {V : Type} [Finite V] (m : MonomialOrder V) (t : Finset V) : IsIrred m ∅ t := by
  intro p hp hn
  exact (hn (ideal_zero p hp)).elim

end SemAC02.Supplement.P2MBooleanEmptyBackground
end

section
-- Inlined Solutions.P2MBoundedOccurrenceRank

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MBoundedOccurrenceRank

open MvPolynomial P2MProofComplexity

def packingBound (d : ℕ) : ℕ := 1 + 2*d + (2*d)^2 + (2*d)^3

theorem nat_bound {L V : Type} [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V]
    (P : ClusteredRep V L V) (m : MonomialOrder V) (hcluster : P.cluster = id) (hF0 : P.F0 = ∅)
    (s : ℝ) (d : ℕ)
    (hL : ∀ u, 2 ≤ (PCNonBool.nbrOn P.graph Finset.univ u).card ∧
      (PCNonBool.nbrOn P.graph Finset.univ u).card ≤ 3)
    (hR : ∀ v, P2MCleaningDegreeReduction.rightDegree P.graph v ≤ d)
    (hstrict : ∀ J : Finset L, J.Nonempty → (J.card : ℝ) ≤ s →
      (J.card : ℝ)/2 < ((PCNonBool.boundaryOn P.graph Finset.univ J).card : ℝ)) (k : ℕ) :
    (Fintype.card V - packingBound d*(k-1))^k ≤ k.factorial * expRank P m s k := by
  classical
  let B := P2MPrimalGraphBalls.ball P.graph 3
  let E := P2MSeparatedSetCounting.sets B k
  have hB : ∀ v, (B v).card ≤ packingBound d := fun v =>
    P2MPrimalGraphBalls.radius_three_card P.graph d (fun u => (hL u).2) hR v
  have hcount := P2MSeparatedSetCounting.count B (packingBound d) hB
    (P2MPrimalGraphBalls.self_mem P.graph 3) (P2MPrimalGraphBalls.ball_symm P.graph 3) k
  have hcl : ∀ v, (Finset.univ.filter (fun x => P.cluster x = v)).card = 1 := by
    intro v
    have he : Finset.univ.filter (fun x => P.cluster x = v) = {v} := by ext x; simp [hcluster]
    rw [he, Finset.card_singleton]
  have hirr : ∀ t : Finset V, (∀ x ∈ t, ∀ y ∈ t, P.cluster x = P.cluster y → x = y) →
      IsIrred m P.F0 t := by
    intro t ht
    rw [hF0]
    exact P2MBooleanEmptyBackground.irreducible m t
  have hk : ∀ A ∈ E, A.card = k := fun A hA => (P2MSeparatedSetCounting.mem_sets B k A).mp hA |>.1
  have hAvoid : ∀ A ∈ E, P2MBoundaryAvoidance.Avoiding P.graph s A := by
    intro A hA
    exact P2MPrimalBoundaryAvoidance.avoiding P.graph s (fun u => (hL u).1) hstrict A
      ((P2MSeparatedSetCounting.mem_sets B k A).mp hA).2
  have hrank := P2MExpansionAvoidingRank.count P m s k 1 hcl hirr E hk hAvoid
  simp only [one_pow, Nat.mul_one] at hrank
  exact hcount.trans (Nat.mul_le_mul_left _ hrank)

theorem bound {L V : Type} [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V]
    (P : ClusteredRep V L V) (m : MonomialOrder V) (hcluster : P.cluster = id) (hF0 : P.F0 = ∅)
    (s : ℝ) (d : ℕ)
    (hL : ∀ u, 2 ≤ (PCNonBool.nbrOn P.graph Finset.univ u).card ∧
      (PCNonBool.nbrOn P.graph Finset.univ u).card ≤ 3)
    (hR : ∀ v, P2MCleaningDegreeReduction.rightDegree P.graph v ≤ d)
    (hstrict : ∀ J : Finset L, J.Nonempty → (J.card : ℝ) ≤ s →
      (J.card : ℝ)/2 < ((PCNonBool.boundaryOn P.graph Finset.univ J).card : ℝ))
    (k : ℕ) (hkn : packingBound d*(k-1) ≤ Fintype.card V) :
    ((Fintype.card V : ℝ) - packingBound d*(k-1 : ℕ))^k / (k.factorial : ℝ) ≤ expRank P m s k := by
  have hh := nat_bound P m hcluster hF0 s d hL hR hstrict k
  have hhR : ((Fintype.card V - packingBound d*(k-1) : ℕ) : ℝ)^k ≤
      (k.factorial : ℝ) * expRank P m s k := by exact_mod_cast hh
  rw [Nat.cast_sub hkn, Nat.cast_mul] at hhR
  apply (div_le_iff₀ (by exact_mod_cast k.factorial_pos : (0 : ℝ) < k.factorial)).mpr
  nlinarith

end SemAC02.Supplement.P2MBoundedOccurrenceRank
end

section
-- Inlined Solutions.P2MBipartiteInducedSubgraph

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MBipartiteInducedSubgraph

open PCNonBool P2MBipartiteNeighborhoodExpansion P2MCleaningDegreeReduction

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def graph (G : BipGraph L R) (I : Finset L) (A : Finset R) :
    BipGraph {u // u ∉ I} {v // v ∉ A} where
  Adj u v := G.Adj u.val v.val

theorem neighbors_image (G : BipGraph L R) (I : Finset L) (A : Finset R)
    (J : Finset {u // u ∉ I}) :
    (neighbors (graph G I A) J).map (Function.Embedding.subtype _) =
      neighbors G (J.map (Function.Embedding.subtype _)) \ A := by
  classical
  ext v
  simp only [Finset.mem_map, mem_neighbors, Finset.mem_sdiff, graph]
  constructor
  · rintro ⟨v', ⟨u, hu, huv⟩, rfl⟩
    exact ⟨⟨u.val, ⟨u, hu, rfl⟩, huv⟩, v'.property⟩
  · rintro ⟨⟨u, ⟨u', hu, rfl⟩, huv⟩, hv⟩
    exact ⟨⟨v, hv⟩, ⟨u', hu, huv⟩, rfl⟩

theorem left_degree (G : BipGraph L R) (I : Finset L) (A : Finset R)
    (u : {u // u ∉ I}) :
    (nbrOn (graph G I A) Finset.univ u).card =
      (nbrOn G (Finset.univ \ A) u.val).card := by
  have hh := congrArg Finset.card (neighbors_image G I A {u})
  have he : nbrOn G Finset.univ u.val \ A = nbrOn G (Finset.univ \ A) u.val := by
    ext v
    simp only [nbrOn, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simpa [neighbors, he] using hh

theorem right_degree (G : BipGraph L R) (I : Finset L) (A : Finset R)
    (v : {v // v ∉ A}) : rightDegree (graph G I A) v ≤ rightDegree G v.val := by
  classical
  have he : (Finset.univ.filter (fun u => (graph G I A).Adj u v)).map
      (Function.Embedding.subtype _) =
      (Finset.univ.filter (fun u => G.Adj u v.val)) \ I := by
    ext u
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, graph]
    constructor
    · rintro ⟨u', hu, rfl⟩
      exact ⟨(Finset.mem_filter.mp hu).2, u'.property⟩
    · rintro ⟨hu, hI⟩
      exact ⟨⟨u, hI⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩
  have hh := congrArg Finset.card he
  simp only [Finset.card_map] at hh
  exact hh.trans_le (Finset.card_le_card Finset.sdiff_subset)

theorem boundary_image (G : BipGraph L R) (I : Finset L) (A : Finset R)
    (J : Finset {u // u ∉ I}) :
    (boundaryOn (graph G I A) Finset.univ J).map (Function.Embedding.subtype _) =
      P2MFiniteFamilyBoundary.boundary (nbrOn G (Finset.univ \ A))
        (J.map (Function.Embedding.subtype _)) := by
  classical
  let J' := J.map (Function.Embedding.subtype (fun u => u ∉ I))
  have hfilter (v : {v // v ∉ A}) :
      (J.filter (fun u => (graph G I A).Adj u v)).map (Function.Embedding.subtype _) =
      J'.filter (fun u => v.val ∈ nbrOn G (Finset.univ \ A) u) := by
    dsimp only [J']
    rw [Finset.filter_map]
    apply congrArg (Finset.map (Function.Embedding.subtype (fun u => u ∉ I)))
    apply Finset.filter_congr
    intro u hu
    simp only [graph, nbrOn, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, v.property, not_false_eq_true]
    rfl

  have hcount (v : {v // v ∉ A}) :
      (J.filter (fun u => (graph G I A).Adj u v)).card =
      P2MFiniteFamilyBoundary.multiplicity (nbrOn G (Finset.univ \ A)) J' v.val := by
    simpa only [Finset.card_map, P2MFiniteFamilyBoundary.multiplicity] using congrArg Finset.card (hfilter v)
  ext v
  simp only [Finset.mem_map, boundaryOn, Finset.mem_filter, Finset.mem_univ, true_and]
  change (∃ v' : {v // v ∉ A},
    (J.filter (fun u => (graph G I A).Adj u v')).card = 1 ∧ v'.val = v) ↔
      v ∈ P2MFiniteFamilyBoundary.boundary (nbrOn G (Finset.univ \ A)) J'
  constructor
  · rintro ⟨v', hv', rfl⟩
    rw [P2MFiniteFamilyBoundary.boundary, Finset.mem_filter]
    refine ⟨?_, by rwa [← hcount]⟩
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega :
      0 < (J.filter (fun u => (graph G I A).Adj u v')).card)
    have hu' := Finset.mem_filter.mp hu
    apply Finset.mem_biUnion.mpr
    refine ⟨u.val, Finset.mem_map.mpr ⟨u, hu'.1, rfl⟩, ?_⟩
    simp only [nbrOn, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨v'.property, hu'.2⟩
  · intro hv
    have hb := (Finset.mem_filter.mp hv).2
    obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hv).1
    have hvA : v ∉ A := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvu).1).2
    exact ⟨⟨v, hvA⟩, (hcount ⟨v, hvA⟩).trans hb, rfl⟩

end P2MProofComplexity.P2MBipartiteInducedSubgraph
end

section
-- Inlined Solutions.P2MRightDegreeReduction

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MRightDegreeReduction

open PCNonBool P2MBipartiteNeighborhoodExpansion P2MCleaningDegreeReduction P2MBipartiteInducedSubgraph

noncomputable def degreeBound (α γ : ℝ) : ℕ := ⌈192 * α / γ⌉₊ + 1

theorem full {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (G : BipGraph L R) (α γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hm : (Fintype.card L : ℝ) ≤ α * Fintype.card R)
    (hlarge : 64 ≤ γ * Fintype.card R)
    (hdeg : ∀ u, (nbrOn G Finset.univ u).card = 3)
    (hExp : Expands G (γ * Fintype.card R) (15/8)) :
    0 < degreeBound α γ ∧ ∃ I : Finset L, ∃ A : Finset R,
      (I.card : ℝ) ≤ γ * Fintype.card R / 4 ∧ I.card < A.card ∧
      (A.card : ℝ) < Fintype.card R / 2 ∧ neighbors G I ⊆ A ∧
      (∀ u, 2 ≤ (nbrOn (graph G I A) Finset.univ u).card ∧
        (nbrOn (graph G I A) Finset.univ u).card ≤ 3) ∧
      (∀ v, rightDegree (graph G I A) v ≤ degreeBound α γ) ∧
      Expands (graph G I A) (γ * Fintype.card R / 2) (7/4) ∧
      (∀ J : Finset {u // u ∉ I}, J.Nonempty →
        (J.card : ℝ) ≤ γ * Fintype.card R / 2 →
        (J.card : ℝ) / 2 < ((boundaryOn (graph G I A) Finset.univ J).card : ℝ)) := by
  classical
  refine ⟨by simp [degreeBound], ?_⟩
  obtain ⟨I, A, hI, hIA, hA, hN, hleft, hright, hExpand, hBoundary⟩ :=
    P2MCleaningDegreeReduction.exists_deletion G α γ hγ hγ1 hm hlarge hdeg hExp
  have hdisj (J : Finset {u // u ∉ I}) :
      Disjoint I (J.map (Function.Embedding.subtype _)) := by
    apply Finset.disjoint_left.mpr
    intro u hu huJ
    obtain ⟨u', _, rfl⟩ := Finset.mem_map.mp huJ
    exact u'.property hu
  refine ⟨I, A, hI, hIA, hA, hN, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [left_degree]
    exact hleft u.val u.property
  · intro v
    have hh := hright v.val v.property
    have hceil : (rightDegree G v.val : ℝ) ≤ ⌈192 * α / γ⌉₊ :=
      hh.trans (Nat.le_ceil _)
    have hn : rightDegree G v.val ≤ ⌈192 * α / γ⌉₊ := by exact_mod_cast hceil
    exact (right_degree G I A v).trans (hn.trans (Nat.le_add_right _ _))
  · intro J hJs
    by_cases hJ : J.Nonempty
    · have hJ' : (J.map (Function.Embedding.subtype (fun u => u ∉ I))).Nonempty :=
        hJ.map
      have hh := hExpand _ (hdisj J) hJ' (by simpa only [Finset.card_map] using hJs)
      have he := congrArg Finset.card (neighbors_image G I A J)
      simp only [Finset.card_map] at he
      simpa only [Finset.card_map, ← he] using hh.le
    · have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      subst J
      simp
  · intro J hJ hJs
    have hJ' : (J.map (Function.Embedding.subtype (fun u => u ∉ I))).Nonempty := hJ.map
    have hh := hBoundary _ (hdisj J) hJ' (by simpa only [Finset.card_map] using hJs)
    have he := congrArg Finset.card (boundary_image G I A J)
    simp only [Finset.card_map] at he
    simpa only [Finset.card_map, ← he] using hh

end P2MProofComplexity.P2MRightDegreeReduction
end

section
-- Inlined Solutions.P2MCNFExpansionPolynomials

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCNFExpansionPolynomials

open MvPolynomial LiftSAParity AC02Frege AC02Frege.P2MBooleanAlgebra

attribute [local instance] Classical.propDecidable

noncomputable def polynomial {V : Type} (C : Clause V) : MvPolynomial V (ZMod 2) :=
  ML (clausePolyF C)

theorem multilinear {V : Type} (C : Clause V) : IsMultilinear (polynomial C) := ml_multilinear _

theorem value {V : Type} (C : Clause V) (x : V → Bool) :
    eval (toF2 x) (polynomial C)=if Falsifies x C then 1 else 0 := by
  rw [polynomial,eval_ml]
  change eval (toF2 x) (∏ l∈C, litPolyF l)=_
  rw [map_prod]
  have hlit (l : V×Bool) : eval (toF2 x) (litPolyF (F:=ZMod 2) l)=if x l.1=l.2 then 0 else 1 := by
    cases hb : l.2 <;> cases hx : x l.1 <;> simp [litPolyF,toF2,hb,hx]
  by_cases hf : Falsifies x C
  · rw [if_pos hf]
    exact Finset.prod_eq_one (fun l hl => (hlit l).trans (if_neg (hf l hl)))
  · rw [if_neg hf]
    unfold Falsifies at hf
    push_neg at hf
    obtain ⟨l,hl,he⟩ := hf
    exact Finset.prod_eq_zero hl ((hlit l).trans (if_pos he))

theorem degree {V : Type} (C : Clause V) : (polynomial C).totalDegree ≤ C.card := by
  apply (AC02Frege.P2MBooleanFlip.ml_totalDegree_le _).trans
  apply (totalDegree_finsetProd C _).trans
  calc
    (∑ l∈C, (litPolyF (F:=ZMod 2) l).totalDegree) ≤ ∑ _l∈C, 1 := by
      apply Finset.sum_le_sum
      intro l hl
      unfold litPolyF
      split_ifs
      · exact (totalDegree_sub _ _).trans (by simp)
      · simp
    _ = C.card := by simp

theorem vars_subset {V : Type} [DecidableEq V] (C : Clause V) :
    (polynomial C).vars⊆C.image Prod.fst := by
  intro x hx
  have hraw := AC02Frege.P2MBooleanRestrictions.ml_vars_subset (clausePolyF (F:=ZMod 2) C) hx
  obtain ⟨l,hl,hxl⟩ := Finset.mem_biUnion.mp (vars_prod _ hraw)
  have hf : (litPolyF (F:=ZMod 2) l).vars⊆{l.1} := by
    unfold litPolyF
    split_ifs
    · simpa using vars_sub_subset (1 : MvPolynomial V (ZMod 2)) (X l.1)
    · simp
  exact Finset.mem_image.mpr ⟨l,hl,(Finset.mem_singleton.mp (hf hxl)).symm⟩

def Consistent {V : Type} (C : Clause V) : Prop :=
  ∀ i, ¬ ((i,true)∈C ∧ (i,false)∈C)

noncomputable def falsifying {V : Type} (C : Clause V) : V → Bool :=
  open Classical in fun i => if (i,true)∈C then false else true

theorem falsifying_spec {V : Type} (C : Clause V) (hC : Consistent C) : Falsifies (falsifying C) C := by
  rintro ⟨i,b⟩ hi
  cases b
  · have hnot : (i,true)∉C := fun hp => hC i ⟨hp,hi⟩
    simp [falsifying,hnot]
  · simp [falsifying,hi]

theorem vars_eq {V : Type} [DecidableEq V] (C : Clause V) (hC : Consistent C) :
    (polynomial C).vars=C.image Prod.fst := by
  apply Finset.Subset.antisymm (vars_subset C)
  intro x hx
  obtain ⟨⟨i,b⟩,hl,he⟩ := Finset.mem_image.mp hx
  dsimp only at he
  subst x
  by_contra hn
  let a := falsifying C
  let a' := Function.update a i b
  have hv : eval (toF2 a) (polynomial C)=1 := by rw [value,if_pos (falsifying_spec C hC)]
  have hnot : ¬ Falsifies a' C := by
    intro hf
    have hh := hf (i,b) hl
    exact hh (by simp [a'])
  have hv' : eval (toF2 a') (polynomial C)=0 := by rw [value,if_neg hnot]
  have heval : eval (toF2 a) (polynomial C)=eval (toF2 a') (polynomial C) := by
    apply eval₂Hom_congr' rfl _ rfl
    intro j hj hj'
    have hji : j≠i := by intro he; subst j; exact hn hj
    simp only [a',Function.update_of_ne hji,toF2]
  rw [hv,hv'] at heval
  exact one_ne_zero heval

theorem wclause_consistent {n w : ℕ} (C : WClause n w) : Consistent C.1 := by
  have hinj : Set.InjOn Prod.fst (↑C.1 : Set (Fin n×Bool)) :=
    (Finset.card_image_iff).mp (C.2.2.trans C.2.1.symm)
  intro i ⟨hp,hn⟩
  have he := hinj hp hn rfl
  have htf : true=false := congrArg Prod.snd he
  cases htf

end SemAC02.Supplement.P2MCNFExpansionPolynomials
end

section
-- Inlined Solutions.P2MExpansionClauseMatching

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MExpansionClauseMatching

open PCNonBool P2MBipartiteNeighborhoodExpansion

theorem matching {L R : Type} [Fintype R] [DecidableEq L] [DecidableEq R]
    (G : BipGraph L R) (I : Finset L) (s a : ℝ)
    (hI : (I.card : ℝ) ≤ s) (ha : 1 ≤ a) (hExp : Expands G s a) :
    ∃ f : I → R, Function.Injective f ∧ ∀ u, G.Adj u.val (f u) := by
  classical
  suffices hh : ∃ f : I → R, Function.Injective f ∧
      ∀ u, f u ∈ nbrOn G Finset.univ u.val by
    simpa only [nbrOn, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun u : I => nbrOn G Finset.univ u.val)).mp
  intro T
  let J := T.map (Function.Embedding.subtype (fun u => u ∈ I))
  have hJI : J ⊆ I := by
    intro u hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hu
    exact x.property
  have hJs : (J.card : ℝ) ≤ s :=
    (by exact_mod_cast Finset.card_le_card hJI : (J.card : ℝ) ≤ I.card).trans hI
  have hN := hExp J hJs
  have hT : J.card = T.card := Finset.card_map _
  have he : neighbors G J = T.biUnion (fun u : I => nbrOn G Finset.univ u.val) := by
    ext v
    simp only [mem_neighbors, J, Finset.mem_map, Finset.mem_biUnion,
      nbrOn, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, ⟨x, hx, rfl⟩, huv⟩
      exact ⟨x, hx, huv⟩
    · rintro ⟨u, hu, huv⟩
      exact ⟨u.val, ⟨u, hu, rfl⟩, huv⟩
  have hcard : (T.card : ℝ) ≤
      ((T.biUnion (fun u : I => nbrOn G Finset.univ u.val)).card : ℝ) := by
    rw [← he, ← hT]
    nlinarith [show (0 : ℝ) ≤ J.card from Nat.cast_nonneg _]
  exact_mod_cast hcard

theorem assignment {L R : Type} [Fintype R] [DecidableEq L] [DecidableEq R]
    (C : L → LiftSAParity.Clause R) (I : Finset L)
    (f : I → R) (hf : Function.Injective f)
    (hmem : ∀ u : I, f u ∈ (C u.val).image Prod.fst) :
    ∃ z : R → Bool, ∀ u ∈ I, ¬ LiftSAParity.Falsifies z (C u) := by
  classical
  have hsign : ∀ u : I, ∃ b : Bool, (f u, b) ∈ C u.val := by
    intro u
    obtain ⟨⟨v, b⟩, hl, he⟩ := Finset.mem_image.mp (hmem u)
    dsimp only at he
    subst v
    exact ⟨b, hl⟩
  choose sign hsign using hsign
  let z : R → Bool := fun v => if h : ∃ u : I, f u = v then sign h.choose else false
  have hz (u : I) : z (f u) = sign u := by
    dsimp [z]
    split_ifs with h
    · have he : h.choose = u := hf h.choose_spec
      rw [he]
    · exact False.elim (h ⟨u, rfl⟩)
  refine ⟨z, ?_⟩
  intro u hu hfalse
  exact hfalse (f ⟨u, hu⟩, sign ⟨u, hu⟩) (hsign ⟨u, hu⟩) (hz ⟨u, hu⟩)

end P2MProofComplexity.P2MExpansionClauseMatching
end

section
-- Inlined Solutions.P2MArithmeticCircuitBasics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MArithmeticCircuitBasics

open MvPolynomial ACirc

lemma toPoly_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) :
    toPoly (.sum ps) = (ps.map (fun p => C p.1*toPoly p.2)).sum := by
  rw [toPoly,List.attach_map_val (f := fun p : F × ACirc F V => C p.1*toPoly p.2)]

lemma toPoly_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) :
    toPoly (.prod cs) = (cs.map toPoly).prod := by
  rw [toPoly,List.attach_map_val]

lemma mem_fold_union {I : Type} [DecidableEq I] (a : I) (Ss : List (Finset I)) :
    a ∈ Ss.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ Ss, a ∈ S := by
  induction Ss with
  | nil => simp
  | cons S Ss ih => simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]; aesop

lemma mem_subterms_prod {F V : Type} (a : ACirc F V) (cs : List (ACirc F V)) :
    a ∈ subterms (.prod cs) ↔ a = .prod cs ∨ ∃ c ∈ cs, a ∈ subterms c := by
  classical
  rw [subterms,List.attach_map_val (f := fun c : ACirc F V => subterms c),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma mem_subterms_sum {F V : Type} (a : ACirc F V) (ps : List (F × ACirc F V)) :
    a ∈ subterms (.sum ps) ↔ a = .sum ps ∨ ∃ p ∈ ps, a ∈ subterms p.2 := by
  classical
  rw [subterms,List.attach_map_val (f := fun p : F × ACirc F V => subterms p.2),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma self_mem_subterms {F V : Type} (c : ACirc F V) : c ∈ subterms c := by
  cases c with
  | var i => simp [subterms]
  | const a => simp [subterms]
  | sum ps => exact (mem_subterms_sum _ _).mpr (Or.inl rfl)
  | prod cs => exact (mem_subterms_prod _ _).mpr (Or.inl rfl)

lemma cval_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) (x : V → Bool) :
    cval (.sum ps) x = (ps.map (fun p => p.1*cval p.2 x)).sum := by
  simp only [cval,polyFn,toPoly_sum,map_list_sum,List.map_map,Function.comp_def,map_mul,eval_C]

lemma cval_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) (x : V → Bool) :
    cval (.prod cs) x = (cs.map (fun c => cval c x)).prod := by
  simp only [cval,polyFn,toPoly_prod,map_list_prod,List.map_map,Function.comp_def]

end SemAC02.Supplement.P2MArithmeticCircuitBasics
end

section
-- Inlined Solutions.P2MProofTopFunctions

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MProofTopFunctions

open ACirc Classical

noncomputable def pool {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    Finset (Ω → F) :=
  ((π.flatMap topTerms).map (fun t => fun x : Ω => cval t x.1)).toFinset.filter (fun g => g≠0)

theorem mem_pool {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) (g : Ω → F) :
    g∈pool Ω π ↔ g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, (fun x : Ω => cval t x.1)=g := by
  constructor
  · intro hp
    have hn := (Finset.mem_filter.mp hp).2
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
    obtain ⟨c,hc,ht⟩ := List.mem_flatMap.mp ht
    exact ⟨hn,c,hc,t,ht,he⟩
  · rintro ⟨hn,c,hc,t,ht,he⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨t,List.mem_flatMap.mpr ⟨c,hc,ht⟩,he⟩),hn⟩

theorem card_eq_topS {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    (pool Ω π).card=topS Ω π := by
  have he : {g : Ω → F | g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, g=fun x => cval t x.1}=
      (↑(pool Ω π) : Set (Ω → F)) := by
    ext g
    rw [Finset.mem_coe,mem_pool]
    constructor
    · rintro ⟨hn,c,hc,t,ht,he⟩; exact ⟨hn,c,hc,t,ht,he.symm⟩
    · rintro ⟨hn,c,hc,t,ht,he⟩; exact ⟨hn,c,hc,t,ht,he.symm⟩
  unfold topS
  rw [he,Set.ncard_coe_finset]

theorem projection_bound {F V U : Type} [CommRing F]
    (η : (U → Bool) → (V → Bool)) (M τ : ACirc F V → ACirc F U)
    (π : List (ACirc F V))
    (hterms : ∀ c, topTerms (M c)=(topTerms c).map τ)
    (hval : ∀ c∈π, ∀ t∈topTerms c, ∀ y, cval (τ t) y=cval t (η y)) :
    topS Set.univ (π.map M) ≤ topS Set.univ π := by
  let pull (f : ↥(Set.univ : Set (V → Bool)) → F) : ↥(Set.univ : Set (U → Bool)) → F :=
    fun y => f ⟨η y.1,Set.mem_univ _⟩
  have hsub : pool Set.univ (π.map M)⊆(pool Set.univ π).image pull := by
    intro g hg
    obtain ⟨hn,c',hc',t',ht',he⟩ := (mem_pool Set.univ (π.map M) g).mp hg
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hc'
    rw [hterms c] at ht'
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ht'
    let f : ↥(Set.univ : Set (V → Bool)) → F := fun x => cval t x.1
    have hpull : pull f=g := by
      rw [←he]
      funext y
      exact (hval c hc t ht y.1).symm
    have hf : f≠0 := by
      intro hz
      apply hn
      rw [←hpull,hz]
      rfl
    exact Finset.mem_image.mpr ⟨f,(mem_pool Set.univ π f).mpr ⟨hf,c,hc,t,ht,rfl⟩,hpull⟩
  rw [←card_eq_topS,←card_eq_topS]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

end SemAC02.Supplement.P2MProofTopFunctions
end

section
-- Inlined Solutions.P2MArithmeticLeafSubstitution

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MArithmeticLeafSubstitution

open ACirc P2MArithmeticCircuitBasics

def liftPoint {V U : Type} (f : V → U ⊕ Bool) (y : U → Bool) : V → Bool :=
  fun i => (f i).elim y id


noncomputable def circuit {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) : ACirc F V → ACirc F U
  | .var i => (f i).elim ACirc.var (fun b => ACirc.const (if b then 1 else 0))
  | .const a => .const a
  | .sum ps => .sum (ps.attach.map (fun p => (p.1.1,circuit f p.1.2)))
  | .prod cs => .prod (cs.attach.map (fun c => circuit f c.1))
termination_by c => c
decreasing_by
  all_goals first
    | (obtain ⟨⟨a,b⟩,hp⟩ := p; have h := List.sizeOf_lt_of_mem hp; simp at h ⊢; omega)
    | (obtain ⟨c,hc⟩ := c; have h := List.sizeOf_lt_of_mem hc; simp at h ⊢; omega)

theorem circuit_sum {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (ps : List (F×ACirc F V)) :
    circuit f (.sum ps)=.sum (ps.map (fun p => (p.1,circuit f p.2))) := by
  rw [circuit,List.attach_map_val (f:=fun p : F×ACirc F V => (p.1,circuit f p.2))]

theorem circuit_prod {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (cs : List (ACirc F V)) :
    circuit f (.prod cs)=.prod (cs.map (circuit f)) := by
  rw [circuit,List.attach_map_val]

theorem value {F V U : Type} [CommRing F] (f : V → U ⊕ Bool) (c : ACirc F V) (y : U → Bool) :
    cval (circuit f c) y=cval c (liftPoint f y) := by
  cases c with
  | var i => cases hi : f i <;> simp [circuit,cval,polyFn,toPoly,boolPt,liftPoint,hi]
  | const a => simp [circuit,cval,polyFn,toPoly]
  | sum ps =>
    rw [circuit_sum,cval_sum,cval_sum,List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    dsimp only [Function.comp_def]
    rw [value f p.2 y]
  | prod cs =>
    rw [circuit_prod,cval_prod,cval_prod,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact value f c y
termination_by c
decreasing_by
  all_goals first
    | (obtain ⟨a,b⟩ := p; have h := List.sizeOf_lt_of_mem hp; simp at h ⊢; omega)
    | (have h := List.sizeOf_lt_of_mem hc; simp at h ⊢; omega)

theorem leaf {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (c : ACirc F V) (hc : IsLeaf c) : IsLeaf (circuit f c) := by
  cases c <;> simp_all [IsLeaf,circuit]
  case var i => cases f i <;> simp [IsLeaf]

theorem sum_of {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (P : ACirc F V → Prop) (Q : ACirc F U → Prop)
    (hPQ : ∀ c, P c → Q (circuit f c)) (c : ACirc F V) (hc : IsSumOf P c) : IsSumOf Q (circuit f c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    rw [circuit_sum]
    rintro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hPQ q.2 (hc q hq)

theorem prod_of {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (P : ACirc F V → Prop) (Q : ACirc F U → Prop)
    (hPQ : ∀ c, P c → Q (circuit f c)) (c : ACirc F V) (hc : IsProdOf P c) : IsProdOf Q (circuit f c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs =>
    rw [circuit_prod]
    intro d hd
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hd
    exact hPQ c (hc c hc')

theorem monomial {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (w : ℕ∞) (c : ACirc F V) (hc : IsMonGate w c) :
    IsMonGate w (circuit f c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs =>
    rw [circuit_prod]
    constructor
    · simpa only [List.length_map] using hc.1
    · intro d hd
      obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hd
      exact leaf f c (hc.2 c hc')

theorem spsp {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (w : ℕ∞) (c : ACirc F V) (hc : IsSPSP w c) :
    IsSPSP w (circuit f c) :=
  sum_of f _ _ (prod_of f _ _ (sum_of f _ _ (monomial f w))) c hc

theorem top_terms {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool) (c : ACirc F V) :
    topTerms (circuit f c)=(topTerms c).map (circuit f) := by
  cases c <;> simp [circuit,circuit_sum,circuit_prod,topTerms,List.map_map,Function.comp_def]
  case var i => cases f i <;> rfl

theorem sps {F V U : Type} [Zero F] [One F] (f : V → U ⊕ Bool)
    (c : ACirc F V) (hc : IsSPS c) : IsSPS (circuit f c) :=
  sum_of f _ _ (prod_of f _ _ (sum_of f _ _ (leaf f))) c hc

theorem top_bound {F V U : Type} [CommRing F] (f : V → U ⊕ Bool)
    (π : List (ACirc F V)) :
    topS Set.univ (π.map (circuit f)) ≤ topS Set.univ π := by
  apply P2MProofTopFunctions.projection_bound (liftPoint f) (circuit f) (circuit f) π (top_terms f)
  intro c hc t ht y
  exact value f t y

end SemAC02.Supplement.P2MArithmeticLeafSubstitution
end

section
-- Inlined Solutions.P2MSemanticLeafSubstitution

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSemanticLeafSubstitution

open ACirc P2MArithmeticLeafSubstitution

theorem refutation {F V U : Type} [Field F] (f : V → U ⊕ Bool)
    (A : Set ((V → Bool) → F)) (B : Set ((U → Bool) → F))
    (P : ACirc F V → Prop) (Q : ACirc F U → Prop)
    (hPQ : ∀ c, P c → Q (circuit f c))
    (hinput : ∀ a ∈ A, (∃ b ∈ B, ∀ y, b y = a (liftPoint f y)) ∨
      (∀ y, a (liftPoint f y) = 0))
    (π : List (ACirc F V)) (hπ : IsSemPCRef P Set.univ A π) :
    IsSemPCRef Q Set.univ B (π.map (circuit f)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact hPQ a (hπ.1 a ha)
  · intro i hi
    have hi' : i < π.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map]
    rcases hπ.2.1 i hi' with ⟨a, ha, he⟩ | he | ⟨j, l, hj, hl, he⟩
    · rcases hinput a ha with ⟨b, hb, hval⟩ | hzero
      · left
        refine ⟨b, hb, ?_⟩
        intro y hy
        rw [value, he _ (Set.mem_univ _), hval y]
      · right; left
        intro y hy
        rw [value, he _ (Set.mem_univ _), hzero y]
    · right; left
      intro y hy
      rw [value]
      exact he _ (Set.mem_univ _)
    · right; right
      refine ⟨j, l, hj, hl, ?_⟩
      intro y hy hp hq
      rw [value] at hp hq ⊢
      exact he _ (Set.mem_univ _) hp hq
  · obtain ⟨c, hc, hval⟩ := hπ.2.2
    refine ⟨circuit f c, ?_, ?_⟩
    · rw [List.getLast?_map, hc]; rfl
    · intro y hy
      rw [value]
      exact hval _ (Set.mem_univ _)

end SemAC02.Supplement.P2MSemanticLeafSubstitution
end

section
-- Inlined Solutions.P2MBooleanFieldPolynomials

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanFieldPolynomials

open MvPolynomial

lemma bool_power {F V : Type} [CommRing F] (x : V → Bool) (i : V) (a : ℕ) :
    (boolPt x i : F)^min a 1=(boolPt x i : F)^a := by
  cases h : x i <;> cases a <;> simp [boolPt,h]

theorem value_mlz {F V : Type} [CommRing F] (p : MvPolynomial V F) : polyFn (mlz p)=polyFn p := by
  classical
  funext x
  change eval (boolPt x) (mlz p)=eval (boolPt x) p
  rw [mlz,map_sum]
  conv_rhs => rw [p.as_sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [eval_monomial,eval_monomial]
  congr 1
  simp only [Finsupp.prod,AC02Frege.P2MBooleanAlgebra.sqfree_support]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [AC02Frege.sqfree,Finsupp.mapRange_apply] using bool_power (F:=F) x i (s i)

lemma monomial_value {F V : Type} [CommRing F] (s : V →₀ ℕ) (a : F) (x : V → Bool) :
    polyFn (monomial s a) x=a*∏ i∈s.support, (boolPt x i : F) := by
  classical
  rw [polyFn,eval_monomial]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have he : s i≠0 := Finsupp.mem_support_iff.mp hi
  cases h : x i <;> simp [boolPt,h,he]

end SemAC02.Supplement.P2MBooleanFieldPolynomials
end

section
-- Inlined Solutions.P2MPolynomialArithmeticCircuits

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPolynomialArithmeticCircuits

open MvPolynomial ACirc P2MArithmeticCircuitBasics

noncomputable def factors {F V : Type} (s : V →₀ ℕ) : List (ACirc F V) :=
  s.support.toList.flatMap (fun i => List.replicate (s i) (.var i))

noncomputable def monomialCircuit {F V : Type} (s : V →₀ ℕ) : ACirc F V := .prod (factors s)

noncomputable def polynomialCircuit {F V : Type} [CommRing F] (p : MvPolynomial V F) : ACirc F V :=
  .sum (p.support.toList.map (fun s => (coeff s p,monomialCircuit s)))

lemma factors_length {F V : Type} (s : V →₀ ℕ) : (factors (F:=F) s).length=s.sum (fun _ e => e) := by
  simp [factors,List.length_flatMap,Finsupp.sum,Finset.sum_toList]

lemma factors_leaves {F V : Type} (s : V →₀ ℕ) : ∀ c∈factors (F:=F) s, IsLeaf c := by
  intro c hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp hc
  trivial

theorem monomial_layer {F V : Type} (s : V →₀ ℕ) (D : ℕ) (hs : s.sum (fun _ e => e) ≤ D) :
    IsMonGate (D : ℕ∞) (monomialCircuit (F:=F) s) := by
  constructor
  · rw [factors_length]
    exact_mod_cast hs
  · exact factors_leaves s

theorem monomial_poly {F V : Type} [CommRing F] (s : V →₀ ℕ) :
    (monomialCircuit (F:=F) s).toPoly=monomial s 1 := by
  classical
  rw [monomialCircuit,toPoly_prod,monomial_eq, C_1,one_mul]
  simp [factors,List.map_flatMap,List.flatMap_def,List.prod_flatten,Finsupp.prod,Finset.prod_map_toList,toPoly]

theorem polynomial_poly {F V : Type} [CommRing F] (p : MvPolynomial V F) :
    (polynomialCircuit p).toPoly=p := by
  rw [polynomialCircuit,toPoly_sum]
  simp only [List.map_map,Function.comp_def,monomial_poly,C_mul_monomial,mul_one]
  rw [Finset.sum_map_toList]
  exact support_sum_monomial_coeff p

theorem polynomial_layer {F V : Type} [CommRing F] (p : MvPolynomial V F) (D : ℕ)
    (hp : p.totalDegree ≤ D) : IsSumOf (IsMonGate (D : ℕ∞)) (polynomialCircuit p) := by
  intro z hz
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
  exact monomial_layer s D ((le_totalDegree (Finset.mem_toList.mp hs)).trans hp)

end SemAC02.Supplement.P2MPolynomialArithmeticCircuits
end

section
-- Inlined Solutions.P2MFieldSelectorProjection

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MFieldSelectorProjection

open MvPolynomial

variable {F V : Type} [Field F] {q : ℕ}

def liftPoint (A : (V×Bool) → Fin q) (x : V → Bool) (z : V×Bool×Fin q) : Bool :=
  if z.2.2=A (z.1,z.2.1) then if z.2.1 then x z.1 else !(x z.1) else false

noncomputable def rho (A : (V×Bool) → Fin q) (z : V×Bool×Fin q) : MvPolynomial V F :=
  if z.2.2=A (z.1,z.2.1) then if z.2.1 then X z.1 else 1-X z.1 else 0

lemma rho_degree (A : (V×Bool) → Fin q) (z : V×Bool×Fin q) : (rho (F:=F) A z).totalDegree ≤ 1 := by
  unfold rho
  split_ifs <;> try simp
  exact (totalDegree_sub _ _).trans (by simp)

lemma rho_value (A : (V×Bool) → Fin q) (x : V → Bool) (z : V×Bool×Fin q) :
    eval (boolPt x) (rho (F:=F) A z)=boolPt (liftPoint A x) z := by
  by_cases h : z.2.2=A (z.1,z.2.1)
  · cases hb : z.2.1 <;> cases hx : x z.1 <;> simp [rho,liftPoint,h,hb,boolPt,hx]
  · simp [rho,liftPoint,h,boolPt]

lemma pair_zero (A : (V×Bool) → Fin q) (x : V → Bool) (z z' : V×Bool×Fin q)
    (hb : z.1=z'.1) (hne : z≠z') :
    (boolPt (liftPoint A x) z : F)=0 ∨ (boolPt (liftPoint A x) z' : F)=0 := by
  by_cases hz : z.2.2=A (z.1,z.2.1)
  · by_cases hz' : z'.2.2=A (z'.1,z'.2.1)
    · have hr : z.2.1≠z'.2.1 := by
        intro he
        apply hne
        apply Prod.ext hb
        apply Prod.ext he
        rw [hz,hz',hb,he]
      rcases z with ⟨i,b,a⟩
      rcases z' with ⟨j,b',a'⟩
      dsimp only at hb hr hz hz' ⊢
      subst j
      cases hx : x i <;> cases b <;> cases b' <;> simp_all [liftPoint,boolPt]
    · exact Or.inr (by simp [liftPoint,hz',boolPt])
  · exact Or.inl (by simp [liftPoint,hz,boolPt])

def Alive (s : (V×Bool×Fin q) →₀ ℕ) (A : (V×Bool) → Fin q) : Prop :=
  (∀ z∈s.support, z.2.2=A (z.1,z.2.1)) ∧
    Set.InjOn (fun z : V×Bool×Fin q => z.1) (s.support : Set (V×Bool×Fin q))

lemma killed (s : (V×Bool×Fin q) →₀ ℕ) (A : (V×Bool) → Fin q) (hdead : ¬ Alive s A)
    (x : V → Bool) : (∏ z∈s.support, (boolPt (liftPoint A x) z : F))=0 := by
  classical
  by_cases hcols : ∀ z∈s.support, z.2.2=A (z.1,z.2.1)
  · have hni : ¬ Set.InjOn (fun z : V×Bool×Fin q => z.1) (s.support : Set (V×Bool×Fin q)) :=
      fun hi => hdead ⟨hcols,hi⟩
    simp only [Set.InjOn,Finset.mem_coe,not_forall,_root_.not_imp] at hni
    obtain ⟨z,hz,z',hz',hb,hne⟩ := hni
    rcases pair_zero (F:=F) A x z z' hb hne with hzero | hzero
    · exact Finset.prod_eq_zero hz hzero
    · exact Finset.prod_eq_zero hz' hzero
  · push_neg at hcols
    obtain ⟨z,hz,hcol⟩ := hcols
    apply Finset.prod_eq_zero hz
    simp [liftPoint,hcol,boolPt]

noncomputable def project [DecidableEq V] (A : (V×Bool) → Fin q) (d : ℕ)
    (p : MvPolynomial (V×Bool×Fin q) F) : MvPolynomial V F :=
  ∑ s∈(mlz p).support.filter (fun s => s.support.card ≤ d),
    C (coeff s (mlz p))*∏ z∈s.support, rho A z

theorem project_degree [DecidableEq V] (A : (V×Bool) → Fin q) (d : ℕ)
    (p : MvPolynomial (V×Bool×Fin q) F) : (project A d p).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C,zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _z∈s.support, 1 := Finset.sum_le_sum (fun z hz => rho_degree A z)
    _ = s.support.card := by simp
    _ ≤ d := (Finset.mem_filter.mp hs).2

theorem project_value [DecidableEq V] (A : (V×Bool) → Fin q) (d : ℕ)
    (p : MvPolynomial (V×Bool×Fin q) F)
    (hgood : ∀ s∈(mlz p).support, d < s.support.card → ¬ Alive s A) (x : V → Bool) :
    polyFn (project A d p) x=polyFn p (liftPoint A x) := by
  classical
  rw [←P2MBooleanFieldPolynomials.value_mlz p]
  change eval (boolPt x) (project A d p)=polyFn (mlz p) (liftPoint A x)
  rw [project,map_sum]
  conv_rhs => rw [(mlz p).as_sum]
  simp only [polyFn,map_sum,P2MBooleanFieldPolynomials.monomial_value]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show eval (boolPt (liftPoint A x)) (monomial s (coeff s (mlz p)))=
      coeff s (mlz p)*∏ z∈s.support, (boolPt (liftPoint A x) z : F) from
    P2MBooleanFieldPolynomials.monomial_value s (coeff s (mlz p)) (liftPoint A x)]
  by_cases hsmall : s.support.card ≤ d
  · simp only [if_pos hsmall,map_mul,eval_C,map_prod,rho_value]
  · simp only [if_neg hsmall]
    rw [killed s A (hgood s hs (by omega)) x,mul_zero]

end SemAC02.Supplement.P2MFieldSelectorProjection
end

section
-- Inlined Solutions.P2MFieldSelectorClauseProjection

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MFieldSelectorClauseProjection

open MvPolynomial LiftSAParity P2MFieldSelectorProjection Classical

lemma literal_value {F V : Type} [Field F] (l : V×Bool) (x : V → Bool) :
    polyFn (litPolyF (F:=F) l) x=if x l.1=l.2 then 0 else 1 := by
  cases hb : l.2 <;> cases hx : x l.1 <;> simp [polyFn,litPolyF,boolPt,hb,hx]

theorem clause_value {F V : Type} [Field F] (C : Clause V) (x : V → Bool) :
    polyFn (clausePolyF (F:=F) C) x=if Falsifies x C then 1 else 0 := by
  classical
  change eval (boolPt x) (∏ l∈C, litPolyF l)=_
  rw [map_prod]
  by_cases hf : Falsifies x C
  · rw [if_pos hf]
    apply Finset.prod_eq_one
    intro l hl
    exact (literal_value (F:=F) l x).trans (if_neg (hf l hl))
  · rw [if_neg hf]
    unfold Falsifies at hf
    push_neg at hf
    obtain ⟨l,hl,he⟩ := hf
    apply Finset.prod_eq_zero hl
    exact (literal_value (F:=F) l x).trans (if_pos he)

lemma lifted_falsifies {V : Type} [DecidableEq V] {q : ℕ}
    (A : (V×Bool) → Fin q) (C : Clause V) (x : V → Bool) :
    Falsifies (liftPoint A x) (C.biUnion (fun l =>
      Finset.univ.image (fun a : Fin q => ((l.1,l.2,a),true)))) ↔ Falsifies x C := by
  constructor
  · intro h l hl
    have hh := h ((l.1,l.2,A (l.1,l.2)),true)
      (Finset.mem_biUnion.mpr ⟨l,hl,Finset.mem_image.mpr ⟨A (l.1,l.2),Finset.mem_univ _,rfl⟩⟩)
    cases hb : l.2 <;> cases hx : x l.1 <;> simp_all [liftPoint]
  · intro h z hz
    obtain ⟨l,hl,hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hh := h l hl
    by_cases hcol : a=A (l.1,l.2)
    · cases hb : l.2 <;> cases hx : x l.1 <;> simp_all [liftPoint]
    · simp [liftPoint,hcol]

lemma selector_satisfied {V : Type} [DecidableEq V] {q : ℕ} (A : (V×Bool) → Fin q) (i : V) (x : V → Bool) :
    ¬ Falsifies (liftPoint A x) (Finset.univ.image (fun c : Bool×Fin q => ((i,c),true))) := by
  intro hf
  have hh := hf ((i,x i,A (i,x i)),true)
    (Finset.mem_image.mpr ⟨(x i,A (i,x i)),Finset.mem_univ _,rfl⟩)
  cases hx : x i <;> simp_all [liftPoint]

lemma exclusion_satisfied {F V : Type} [Field F] [DecidableEq V] {q : ℕ} (A : (V×Bool) → Fin q) (i : V)
    (S : Finset (Bool×Fin q)) (hS : S.card=2) (x : V → Bool) :
    ¬ Falsifies (liftPoint A x) (S.image (fun c => ((i,c),false))) := by
  classical
  intro hf
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hS
  have ha := hf ((i,a),false) (Finset.mem_image.mpr ⟨a,by simp,rfl⟩)
  have hb := hf ((i,b),false) (Finset.mem_image.mpr ⟨b,by simp,rfl⟩)
  have ha' : liftPoint A x (i,a)=true := Bool.eq_true_of_not_eq_false ha
  have hb' : liftPoint A x (i,b)=true := Bool.eq_true_of_not_eq_false hb
  rcases pair_zero (F:=F) A x (i,a) (i,b) rfl (by intro he; exact hab (Prod.mk.inj he).2) with h | h
  · exact one_ne_zero (by simpa only [boolPt,ha',↓reduceIte] using h)
  · exact one_ne_zero (by simpa only [boolPt,hb',↓reduceIte] using h)

theorem input_projection {F : Type} [Field F] {n q : ℕ} (A : (Fin n×Bool) → Fin q)
    (base : List (Clause (Fin n))) (C : Clause (Fin n×Bool×Fin q)) (hC : C∈selLift q base) :
    (∃ D∈base, ∀ x, polyFn (clausePolyF (F:=F) C) (liftPoint A x)=polyFn (clausePolyF D) x) ∨
      (∀ x, polyFn (clausePolyF (F:=F) C) (liftPoint A x)=0) := by
  classical
  simp only [selLift,List.mem_append,List.mem_map,List.mem_flatMap] at hC
  rcases hC with (⟨i,hi,rfl⟩ | ⟨i,hi,S,hS,rfl⟩) | ⟨D,hD,rfl⟩
  · right
    intro x
    simp only [clause_value,if_neg (selector_satisfied A i x)]
  · right
    intro x
    have hcard : S.card=2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hS)).2
    simp only [clause_value,if_neg (exclusion_satisfied (F:=F) A i S hcard x)]
  · left
    refine ⟨D,hD,?_⟩
    intro x
    rw [clause_value,clause_value,lifted_falsifies]

end SemAC02.Supplement.P2MFieldSelectorClauseProjection
end

section
-- Inlined Solutions.P2MCNFPartialRestriction

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MCNFPartialRestriction

open LiftSAParity ACirc P2MArithmeticLeafSubstitution

variable {V : Type} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

def substitution (A : Finset V) (z : V → Bool) (v : V) : {v // v ∉ A} ⊕ Bool :=
  if h : v ∈ A then .inr (z v) else .inl ⟨v, h⟩

noncomputable def clause (A : Finset V) (C : Clause V) : Clause {v // v ∉ A} :=
  Finset.univ.filter (fun l => (l.1.val, l.2) ∈ C)

def SatisfiedOn (A : Finset V) (z : V → Bool) (C : Clause V) : Prop :=
  ∃ l ∈ C, l.1 ∈ A ∧ z l.1 = l.2

@[simp] theorem mem_clause (A : Finset V) (C : Clause V) (l : {v // v ∉ A} × Bool) :
    l ∈ clause A C ↔ (l.1.val, l.2) ∈ C := by simp [clause]

theorem lift_assigned (A : Finset V) (z : V → Bool) (y : {v // v ∉ A} → Bool)
    (v : V) (hv : v ∈ A) : liftPoint (substitution A z) y v = z v := by
  simp [liftPoint, substitution, hv]

theorem lift_free (A : Finset V) (z : V → Bool) (y : {v // v ∉ A} → Bool)
    (v : {v // v ∉ A}) : liftPoint (substitution A z) y v.val = y v := by
  simp [liftPoint, substitution, v.property]

theorem satisfied (A : Finset V) (z : V → Bool) (C : Clause V)
    (hC : SatisfiedOn A z C) (y : {v // v ∉ A} → Bool) :
    ¬ Falsifies (liftPoint (substitution A z) y) C := by
  obtain ⟨l, hl, hA, hz⟩ := hC
  intro hf
  exact hf l hl ((lift_assigned A z y l.1 hA).trans hz)

theorem falsifies (A : Finset V) (z : V → Bool) (C : Clause V)
    (hC : ¬ SatisfiedOn A z C) (y : {v // v ∉ A} → Bool) :
    Falsifies (liftPoint (substitution A z) y) C ↔ Falsifies y (clause A C) := by
  constructor
  · intro hf l hl
    have hh := hf (l.1.val, l.2) ((mem_clause A C l).mp hl)
    rwa [lift_free] at hh
  · intro hf l hl
    by_cases hA : l.1 ∈ A
    · rw [lift_assigned A z y l.1 hA]
      intro he
      exact hC ⟨l, hl, hA, he⟩
    · have hh := hf (⟨l.1, hA⟩, l.2) ((mem_clause A C _).mpr hl)
      change liftPoint (substitution A z) y (⟨l.1, hA⟩ : {v // v ∉ A}).val ≠ l.2
      rw [lift_free]
      exact hh

theorem consistent (A : Finset V) (C : Clause V) (hC : P2MCNFExpansionPolynomials.Consistent C) :
    P2MCNFExpansionPolynomials.Consistent (clause A C) := by
  intro v ⟨hp, hn⟩
  exact hC v.val ⟨(mem_clause A C _).mp hp, (mem_clause A C _).mp hn⟩

theorem variables_image (A : Finset V) (C : Clause V) :
    ((clause A C).image Prod.fst).map (Function.Embedding.subtype _) = C.image Prod.fst \ A := by
  classical
  ext v
  simp only [Finset.mem_map, Finset.mem_image, mem_clause, Finset.mem_sdiff]
  constructor
  · rintro ⟨v', ⟨⟨w, b⟩, hl, he⟩, rfl⟩
    dsimp only at he
    subst w
    exact ⟨⟨(v'.val, b), hl, rfl⟩, v'.property⟩
  · rintro ⟨⟨⟨w, b⟩, hl, he⟩, hv⟩
    dsimp only at he
    subst w
    exact ⟨⟨v, hv⟩, ⟨(⟨v, hv⟩, b), hl, rfl⟩, rfl⟩

theorem input_projection (A : Finset V) (z : V → Bool) (S : Set (Clause V)) :
    ∀ a ∈ clauseAx (F:=ZMod 2) S,
      (∃ b ∈ clauseAx (F:=ZMod 2) (clause A '' {C ∈ S | ¬ SatisfiedOn A z C}),
        ∀ y, b y = a (liftPoint (substitution A z) y)) ∨
      (∀ y, a (liftPoint (substitution A z) y) = 0) := by
  rintro a ⟨C, hCS, rfl⟩
  by_cases hC : SatisfiedOn A z C
  · right
    intro y
    rw [P2MFieldSelectorClauseProjection.clause_value, if_neg (satisfied A z C hC y)]
  · left
    refine ⟨polyFn (clausePolyF (clause A C)), ⟨clause A C, ⟨C, ⟨hCS, hC⟩, rfl⟩, rfl⟩, ?_⟩
    intro y
    rw [P2MFieldSelectorClauseProjection.clause_value, P2MFieldSelectorClauseProjection.clause_value,
      falsifies A z C hC y]

theorem refutation (A : Finset V) (z : V → Bool) (S : Set (Clause V))
    (π : List (ACirc (ZMod 2) V))
    (hπ : IsSemPCRef IsSPS Set.univ (clauseAx S) π) :
    IsSemPCRef IsSPS Set.univ
      (clauseAx (clause A '' {C ∈ S | ¬ SatisfiedOn A z C}))
      (π.map (circuit (substitution A z))) :=
  P2MSemanticLeafSubstitution.refutation (substitution A z) _ _ _ _
    (sps (substitution A z)) (input_projection A z S) π hπ

end SemAC02.Supplement.P2MCNFPartialRestriction
end

section
-- Inlined Solutions.P2MClusterPolynomialEvaluation

namespace SemAC02.Supplement.P2MClusterPolynomialEvaluation

open MvPolynomial

theorem evaluation {σ L R : Type} [DecidableEq R] (P : ClusteredRep σ L R) (v : R)
    (α y : σ → ZMod 2) (p : MvPolynomial σ (ZMod 2)) :
    eval y (P.substCluster v α p)=eval (fun x => if P.cluster x=v then α x else y x) p := by
  classical
  let φ : MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] MvPolynomial σ (ZMod 2) :=
    aeval (fun x => if P.cluster x=v then C (α x) else X x)
  have hsub : P.substCluster v α p=φ p := by
    unfold ClusteredRep.substCluster
    apply congrArg (fun f : σ → MvPolynomial σ (ZMod 2) => aeval f p)
    funext x
    by_cases h : P.cluster x=v <;> simp [φ,h]
  rw [hsub]
  change ((eval y).comp φ.toRingHom) p=(eval (fun x => if P.cluster x=v then α x else y x)) p
  apply hom_congr_vars
  · ext a; simp [φ]
  · intro x hx hx'
    by_cases h : P.cluster x=v <;> simp [φ,h]
  · rfl

end SemAC02.Supplement.P2MClusterPolynomialEvaluation
end

section
-- Inlined Solutions.P2MExpansionCNFRepresentation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionCNFRepresentation

open MvPolynomial LiftSAParity AC02Frege AC02Frege.P2MBooleanAlgebra P2MCNFExpansionPolynomials

variable {V I : Type} [Finite V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def representation (C : I → Clause V) : ClusteredRep V I V where
  F0 := ∅
  Fu := fun u => {polynomial (C u)}
  cluster := id

theorem multilinear (C : I → Clause V) : ∀ p∈(representation C).axioms, IsMultilinear p := by
  rintro p (hp | ⟨u,hp⟩)
  · simp [representation] at hp
  · have he : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
    rw [he]
    exact P2MCNFExpansionPolynomials.multilinear _

theorem degrees (C : I → Clause V) (w : ℕ) (hw : ∀ u, (C u).card ≤ w) :
    ∀ p∈(representation C).axioms, p.totalDegree ≤ w := by
  rintro p (hp | ⟨u,hp⟩)
  · simp [representation] at hp
  · have he : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
    rw [he]
    exact (P2MCNFExpansionPolynomials.degree _).trans (hw u)

theorem graph_iff (C : I → Clause V) (hC : ∀ u, Consistent (C u)) (u : I) (v : V) :
    (representation C).graph.Adj u v ↔ v∈(C u).image Prod.fst := by
  constructor
  · rintro ⟨p,hp,x,hx,he⟩
    have hp' : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
    have he' : x=v := he
    subst x
    rw [hp',P2MCNFExpansionPolynomials.vars_eq _ (hC u)] at hx
    exact hx
  · intro hv
    exact ⟨polynomial (C u),Set.mem_singleton _,v,by rwa [P2MCNFExpansionPolynomials.vars_eq _ (hC u)],rfl⟩

theorem respectful (C : I → Clause V) (hC : ∀ u, Consistent (C u)) :
    (representation C).IsRespectful := by
  intro J v u hboundary
  have hu : u∈J.filter (fun a => (representation C).graph.Adj a v) := by rw [hboundary]; simp
  have hv := (graph_iff C hC u v).mp (Finset.mem_filter.mp hu).2
  obtain ⟨⟨x,b⟩,hl,he⟩ := Finset.mem_image.mp hv
  dsimp only at he
  subst x
  refine ⟨fun _ => if b then 1 else 0,?_,?_⟩
  · intro p hp y
    have hp' : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
    rw [hp']
    let z : V → Bool := Function.update y v b
    have heval : eval (toF2 y) ((representation C).substCluster v (fun _ => if b then 1 else 0)
        (polynomial (C u)))=eval (toF2 z) (polynomial (C u)) := by
      rw [P2MClusterPolynomialEvaluation.evaluation]
      apply congrArg (fun f : V → ZMod 2 => eval f (polynomial (C u)))
      funext i
      by_cases hiv : i=v
      · subst i
        simp [representation,toF2,z]
      · simp [representation,hiv,toF2,z,Function.update_of_ne hiv]
    rw [heval,P2MCNFExpansionPolynomials.value]
    apply if_neg
    intro hf
    exact hf (v,b) hl (by simp [z])
  · intro g hg
    simp [representation] at hg

theorem encoded_axioms (C : I → Clause V) :
    polyAx (representation C).axioms=clauseAx (Set.range C) := by
  ext f
  constructor
  · rintro ⟨p,(hp | ⟨u,hp⟩),rfl⟩
    · simp [representation] at hp
    · have hp' : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
      refine ⟨C u,⟨u,rfl⟩,?_⟩
      rw [hp']
      funext y
      exact eval_ml _ _
  · rintro ⟨D,⟨u,rfl⟩,rfl⟩
    refine ⟨polynomial (C u),Or.inr ⟨u,Set.mem_singleton _⟩,?_⟩
    funext y
    exact eval_ml _ _

theorem explicit_boundary [Fintype V] (C : I → Clause V) (hC : ∀ i, Consistent (C i)) (J : Finset I) :
    PCNonBool.boundaryOn (representation C).graph Finset.univ J=
      Finset.univ.filter (fun v : V => (J.filter (fun j => v∈(C j).image Prod.fst)).card=1) := by
  apply Finset.filter_congr
  intro v hv
  have hf : J.filter (fun j => (representation C).graph.Adj j v)=
      J.filter (fun j => v∈(C j).image Prod.fst) :=
    Finset.filter_congr (fun j hj => graph_iff C hC j v)
  rw [hf]

end SemAC02.Supplement.P2MExpansionCNFRepresentation
end

section
-- Inlined Solutions.P2MCNFCleaningFamilies

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MCNFCleaningFamilies

open LiftSAParity P2MProofComplexity PCNonBool P2MExpansionCNFRepresentation P2MCNFPartialRestriction
open P2MBipartiteNeighborhoodExpansion

attribute [local instance] Classical.propDecidable

variable {L V : Type} [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V]

theorem consistent_card (C : Clause V) (hC : P2MCNFExpansionPolynomials.Consistent C) :
    (C.image Prod.fst).card = C.card := by
  apply Finset.card_image_iff.mpr
  rintro ⟨v, b⟩ hb ⟨w, c⟩ hc he
  dsimp only at he
  subst w
  have hbc : b = c := by
    cases b <;> cases c <;> try rfl
    · exact (hC v ⟨hc, hb⟩).elim
    · exact (hC v ⟨hb, hc⟩).elim
  subst c
  rfl

noncomputable def family (C : L → Clause V) (I : Finset L) (A : Finset V) :
    {u // u ∉ I} → Clause {v // v ∉ A} := fun u => clause A (C u.val)

theorem family_consistent (C : L → Clause V) (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u))
    (I : Finset L) (A : Finset V) : ∀ u, P2MCNFExpansionPolynomials.Consistent (family C I A u) :=
  fun u => P2MCNFPartialRestriction.consistent A (C u.val) (hC u.val)

theorem mem_variable (A : Finset V) (C : Clause V) (v : {v // v ∉ A}) :
    v ∈ (clause A C).image Prod.fst ↔ v.val ∈ C.image Prod.fst := by
  constructor
  · intro hv
    obtain ⟨⟨w, b⟩, hl, he⟩ := Finset.mem_image.mp hv
    dsimp only at he
    subst w
    exact Finset.mem_image.mpr ⟨(v.val, b), (mem_clause A C _).mp hl, rfl⟩
  · intro hv
    obtain ⟨⟨w, b⟩, hl, he⟩ := Finset.mem_image.mp hv
    dsimp only at he
    subst w
    exact Finset.mem_image.mpr ⟨(v, b), (mem_clause A C _).mpr hl, rfl⟩

theorem graph_eq (C : L → Clause V) (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u))
    (I : Finset L) (A : Finset V) :
    (representation (family C I A)).graph =
      P2MBipartiteInducedSubgraph.graph (representation C).graph I A := by
  have hadj : (representation (family C I A)).graph.Adj =
      (P2MBipartiteInducedSubgraph.graph (representation C).graph I A).Adj := by
    funext u v
    apply propext
    rw [P2MExpansionCNFRepresentation.graph_iff _ (family_consistent C hC I A)]
    change v ∈ (clause A (C u.val)).image Prod.fst ↔ (representation C).graph.Adj u.val v.val
    rw [mem_variable, P2MExpansionCNFRepresentation.graph_iff C hC]
  cases he : (representation (family C I A)).graph with
  | mk adj =>
    cases hf : (P2MBipartiteInducedSubgraph.graph (representation C).graph I A) with
    | mk adj' =>
      simp only [he, hf] at hadj
      cases hadj
      congr

theorem family_width (C : L → Clause V) (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u))
    (I : Finset L) (A : Finset V) (u : {u // u ∉ I}) :
    (family C I A u).card = (nbrOn (P2MBipartiteInducedSubgraph.graph (representation C).graph I A)
      Finset.univ u).card := by
  rw [← graph_eq C hC I A, ← consistent_card _ (family_consistent C hC I A u)]
  congr 1
  ext v
  simp only [nbrOn, Finset.mem_filter, Finset.mem_univ, true_and,
    P2MExpansionCNFRepresentation.graph_iff _ (family_consistent C hC I A)]

theorem refutation (C : L → Clause V) (I : Finset L) (A : Finset V) (z : V → Bool)
    (hz : ∀ u ∈ I, SatisfiedOn A z (C u))
    (π : List (ACirc (ZMod 2) V))
    (hπ : IsSemPCRef ACirc.IsSPS Set.univ (clauseAx (Set.range C)) π) :
    IsSemPCRef ACirc.IsSPS Set.univ (clauseAx (Set.range (family C I A)))
      (π.map (P2MArithmeticLeafSubstitution.circuit (substitution A z))) := by
  apply P2MSemanticLeafSubstitution.refutation (substitution A z) _ _ _ _
    (P2MArithmeticLeafSubstitution.sps (substitution A z)) _ π hπ
  rintro a ⟨D, ⟨u, rfl⟩, rfl⟩
  by_cases hsat : SatisfiedOn A z (C u)
  · right
    intro y
    rw [P2MFieldSelectorClauseProjection.clause_value, if_neg (satisfied A z (C u) hsat y)]
  · have hu : u ∉ I := fun hu => hsat (hz u hu)
    left
    refine ⟨polyFn (clausePolyF (family C I A ⟨u, hu⟩)),
      ⟨family C I A ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, rfl⟩, ?_⟩
    intro y
    dsimp only [family]
    rw [P2MFieldSelectorClauseProjection.clause_value, P2MFieldSelectorClauseProjection.clause_value,
      falsifies A z (C u) hsat y]

theorem prepared_family (C : L → Clause V) (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u))
    (hwidth : ∀ u, (C u).card = 3) (α γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hm : (Fintype.card L : ℝ) ≤ α * Fintype.card V)
    (hlarge : 64 ≤ γ * Fintype.card V)
    (hExp : Expands (representation C).graph (γ * Fintype.card V) (15/8)) :
    ∃ I : Finset L, ∃ A : Finset V, ∃ z : V → Bool,
      (A.card : ℝ) < Fintype.card V / 2 ∧
      (∀ u ∈ I, SatisfiedOn A z (C u)) ∧
      (∀ u, 2 ≤ (family C I A u).card ∧ (family C I A u).card ≤ 3) ∧
      (∀ v, P2MCleaningDegreeReduction.rightDegree (representation (family C I A)).graph v ≤
        P2MRightDegreeReduction.degreeBound α γ) ∧
      (∀ J : Finset {u // u ∉ I}, J.Nonempty →
        (J.card : ℝ) ≤ γ * Fintype.card V / 2 →
        (J.card : ℝ) / 2 <
          ((boundaryOn (representation (family C I A)).graph Finset.univ J).card : ℝ)) := by
  have hdeg (u : L) : (nbrOn (representation C).graph Finset.univ u).card = 3 := by
    have he : nbrOn (representation C).graph Finset.univ u = (C u).image Prod.fst := by
      ext v
      simp only [nbrOn, Finset.mem_filter, Finset.mem_univ, true_and,
        P2MExpansionCNFRepresentation.graph_iff C hC]
    rw [he, consistent_card _ (hC u), hwidth u]
  obtain ⟨hd, I, A, hI, hIA, hA, hN, hleft, hright, hexp, hboundary⟩ :=
    P2MRightDegreeReduction.full (representation C).graph α γ hγ hγ1 hm hlarge hdeg hExp
  have hIs : (I.card : ℝ) ≤ γ * Fintype.card V := by linarith
  obtain ⟨f, hf, hfadj⟩ := P2MExpansionClauseMatching.matching (representation C).graph I
    (γ * Fintype.card V) (15/8) hIs (by norm_num) hExp
  obtain ⟨z, hz⟩ := P2MExpansionClauseMatching.assignment C I f hf
    (fun u => (P2MExpansionCNFRepresentation.graph_iff C hC u.val (f u)).mp (hfadj u))
  have hzA : ∀ u ∈ I, SatisfiedOn A z (C u) := by
    intro u hu
    by_contra hn
    apply hz u hu
    intro l hl he
    have hv : l.1 ∈ neighbors (representation C).graph I := by
      apply (mem_neighbors _ _ _).mpr
      exact ⟨u, hu, (P2MExpansionCNFRepresentation.graph_iff C hC u l.1).mpr
        (Finset.mem_image.mpr ⟨l, hl, rfl⟩)⟩
    exact hn ⟨l, hl, hN hv, he⟩
  refine ⟨I, A, z, hA, hzA, ?_, ?_, ?_⟩
  · intro u
    rw [family_width C hC I A u]
    exact hleft u
  · rw [graph_eq C hC I A]
    exact hright
  · rw [graph_eq C hC I A]
    exact hboundary

end SemAC02.Supplement.P2MCNFCleaningFamilies
end

section
-- Inlined Solutions.P2MStrictBoundaryExpansion

namespace P2MProofComplexity.P2MStrictBoundaryExpansion

theorem margin {L R : Type} [Fintype R]
    (G : PCNonBool.BipGraph L R) (s : ℝ) (hs : 0 < s)
    (hstrict : ∀ J : Finset L, J.Nonempty → (J.card : ℝ) ≤ s →
      (J.card : ℝ) / 2 < ((PCNonBool.boundaryOn G Finset.univ J).card : ℝ)) :
    (1/2 : ℝ) < 1/2 + 1/(2*s) ∧
      SemAC02.Supplement.IsBdryExp G s (1/2 + 1/(2*s)) := by
  have hp : (0 : ℝ) < 1/(2*s) := by positivity
  refine ⟨by linarith, ?_⟩
  intro J hJs
  by_cases hJ : J.Nonempty
  · have hh := hstrict J hJ hJs
    have hnat : J.card < 2 * (PCNonBool.boundaryOn G Finset.univ J).card := by
      exact_mod_cast (show (J.card : ℝ) < 2 * (PCNonBool.boundaryOn G Finset.univ J).card by linarith)
    have hnat' : J.card + 1 ≤ 2 * (PCNonBool.boundaryOn G Finset.univ J).card := hnat
    have hreal : (J.card : ℝ) + 1 ≤ 2 * (PCNonBool.boundaryOn G Finset.univ J).card := by
      exact_mod_cast hnat'
    have hdiv : (J.card : ℝ)/(2*s) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*s)).mpr
      linarith
    have he : (1/2 + 1/(2*s)) * (J.card : ℝ) = (J.card : ℝ)/2 + (J.card : ℝ)/(2*s) := by ring
    rw [he]
    linarith
  · have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    simp

end P2MProofComplexity.P2MStrictBoundaryExpansion
end

section
-- Inlined Solutions.P2MDegreeCompatibleOrder

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDegreeCompatibleOrder

open MvPolynomial

lemma exponent_sum_mono {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (a b : σ →₀ ℕ) (hab : m.toSyn a ≤ m.toSyn b) : Finsupp.degree a ≤ Finsupp.degree b := by
  by_contra hn
  exact (not_lt_of_ge hab) (hm b a (lt_of_not_ge hn))

theorem totalDegree_eq {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (p : MvPolynomial σ (ZMod 2)) : p.totalDegree=Finsupp.degree (m.degree p) := by
  by_cases hz : p=0
  · subst p
    simp
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    exact exponent_sum_mono m hm d (m.degree p) (m.le_degree hd)
  · exact le_totalDegree (m.degree_mem_support hz)

theorem totalDegree_mono {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (p q : MvPolynomial σ (ZMod 2)) (hle : m.toSyn (m.degree p) ≤ m.toSyn (m.degree q)) :
    p.totalDegree ≤ q.totalDegree := by
  rw [totalDegree_eq m hm p,totalDegree_eq m hm q]
  exact exponent_sum_mono m hm _ _ hle

end SemAC02.Supplement.P2MDegreeCompatibleOrder
end

section
-- Inlined Solutions.P2MDegreeLexCompatibility

namespace SemAC02.Supplement.P2MDegreeLexCompatibility

theorem compatible {σ : Type} [LinearOrder σ] [WellFoundedGT σ] :
    IsDegCompatible (MonomialOrder.degLex : MonomialOrder σ) := by
  intro a b hab
  change toDegLex a < toDegLex b
  rw [Finsupp.DegLex.lt_iff]
  exact Or.inl hab

end SemAC02.Supplement.P2MDegreeLexCompatibility
end

section
-- Inlined Solutions.P2MBoundedCNFOperatorWitness

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MBoundedCNFOperatorWitness

open MvPolynomial AC02Frege LiftSAParity P2MProofComplexity P2MExpansionCNFRepresentation

theorem exists_reduction {n : ℕ} {L : Type} [Fintype L] [DecidableEq L]
    (C : L → Clause (Fin n)) (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u))
    (hwidth : ∀ u, 2 ≤ (C u).card ∧ (C u).card ≤ 3)
    (d : ℕ) (hR : ∀ v, P2MCleaningDegreeReduction.rightDegree (representation C).graph v ≤ d)
    (s : ℝ) (hs : 1 ≤ s)
    (hstrict : ∀ J : Finset L, J.Nonempty → (J.card : ℝ) ≤ s →
      (J.card : ℝ)/2 < ((PCNonBool.boundaryOn (representation C).graph Finset.univ J).card : ℝ))
    (K k : ℕ) (hK3 : 3 ≤ K) (hK : (K : ℝ)+1 ≤ s/4) (hkK : k ≤ K)
    (hkn : P2MBoundedOccurrenceRank.packingBound d*(k-1) ≤ n) :
    ∃ R : Ble (Fin n) K →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2),
      IsPseudoRed (representation C).axioms R ∧
      ((n : ℝ)-P2MBoundedOccurrenceRank.packingBound d*(k-1 : ℕ))^k / (k.factorial : ℝ) ≤ rankLe R k := by
  classical
  let P := representation C
  let c : ℝ := 1/2 + 1/(2*s)
  obtain ⟨hc, hexp⟩ := P2MStrictBoundaryExpansion.margin P.graph s (by linarith) hstrict
  have hzero : ∃ y : Fin n → Bool, ∀ g ∈ P.F0, eval (toF2 y) g = 0 := by
    refine ⟨fun _ => false, ?_⟩
    intro g hg
    exact hg.elim
  have hdegree : ∀ p ∈ P.axioms, p.totalDegree ≤ K := fun p hp =>
    (degrees C 3 (fun u => (hwidth u).2) p hp).trans hK3
  have hbudget : (K : ℝ)+1 ≤ c*s/2 := by
    have hp := mul_le_mul_of_nonneg_right hc.le (by linarith : (0 : ℝ) ≤ s/2)
    dsimp [c]
    nlinarith
  obtain ⟨R, hPseudo, hDeg, hMono, hRank, hOne⟩ := lemma_5_3_expansion_pseudo_reduction P
    MonomialOrder.degLex P2MDegreeLexCompatibility.compatible (multilinear C) hzero (respectful C hC)
    s c hs (by dsimp [c]; linarith) hexp K hdegree hbudget
  refine ⟨R, hPseudo, ?_⟩
  rw [hRank k hkK]
  have hL (u : L) : 2 ≤ (PCNonBool.nbrOn P.graph Finset.univ u).card ∧
      (PCNonBool.nbrOn P.graph Finset.univ u).card ≤ 3 := by
    have he : PCNonBool.nbrOn P.graph Finset.univ u = (C u).image Prod.fst := by
      ext v
      simp only [PCNonBool.nbrOn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact P2MExpansionCNFRepresentation.graph_iff C hC u v
    rw [he, P2MCNFCleaningFamilies.consistent_card _ (hC u)]
    exact hwidth u
  simpa only [Fintype.card_fin] using P2MBoundedOccurrenceRank.bound P MonomialOrder.degLex rfl rfl
    s d hL hR hstrict k (by simpa only [Fintype.card_fin] using hkn)

end SemAC02.Supplement.P2MBoundedCNFOperatorWitness
end

section
-- Inlined Solutions.P2MBoundedCNFRankRatio

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MBoundedCNFRankRatio

theorem power_exponential (n k : ℕ) (hn : 1 ≤ n) (hkn : k ≤ n) :
    Real.exp ((k : ℝ)^2/(2*n)) ≤ (1+(k : ℝ)/n)^k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let t : ℝ := (k : ℝ)/n
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hnR).mpr
    simpa only [one_mul] using (show (k : ℝ) ≤ n by exact_mod_cast hkn)
  have hlog : t/2 ≤ Real.log (1+t) := by
    have hh := Real.le_log_one_add_of_nonneg ht0
    have hlow : t/2 ≤ 2*t/(t+2) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < t+2)).mpr
      nlinarith
    exact hlow.trans hh
  have he : Real.exp ((k : ℝ)*Real.log (1+t)) = (1+t)^k := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < 1+t)]
  rw [← he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have he' : (k : ℝ)^2/(2*n) = (k : ℝ)*(t/2) := by dsimp [t]; field_simp <;> ring
  rwa [he']

theorem lower (n b k : ℕ) (hk : 1 ≤ k) (hbudget : 3*(k+(b+1)*k) ≤ n)
    (rank : ℝ)
    (hrank : ((n : ℝ)-(b : ℝ)*(k-1 : ℕ))^k/(k.factorial : ℝ) ≤ rank) :
    1/2*Real.exp ((k : ℝ)^2/(2*n)) ≤ rank/(2*((n-(b+1)*k).choose k : ℝ)) := by
  let r := (b+1)*k
  have hr : r ≤ n := by dsimp [r]; omega
  have hknr : k ≤ n-r := by dsimp [r]; omega
  have hkn : k ≤ n := by omega
  have hn : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsub : ((n-r : ℕ) : ℝ) = (n : ℝ)-r := Nat.cast_sub hr
  have hrR : (r : ℝ) = ((b : ℝ)+1)*k := by dsimp [r]; push_cast; rfl
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkSub : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by rw [Nat.cast_sub hk]; norm_num
  have hbase0 : 0 ≤ ((n-r : ℕ) : ℝ)*(1+(k : ℝ)/n) := by positivity
  have hbase : ((n-r : ℕ) : ℝ)*(1+(k : ℝ)/n) ≤
      (n : ℝ)-(b : ℝ)*(k-1 : ℕ) := by
    have hsmall : ((n-r : ℕ) : ℝ)*((k : ℝ)/n) ≤ k := by
      have hnr : ((n-r : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n r
      calc
        _ ≤ (n : ℝ)*((k : ℝ)/n) := mul_le_mul_of_nonneg_right hnr (by positivity)
        _ = _ := by field_simp
    rw [hsub, hkSub]
    rw [hsub] at hsmall
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    nlinarith [hrR]
  have hpow := pow_le_pow_left₀ hbase0 hbase k
  rw [mul_pow] at hpow
  have hchoose : ((n-r).choose k : ℝ) ≤ ((n-r : ℕ) : ℝ)^k/(k.factorial : ℝ) :=
    Nat.choose_le_pow_div k (n-r)
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hcomb : ((n-r).choose k : ℝ)*(1+(k : ℝ)/n)^k ≤ rank := by
    calc
      _ ≤ (((n-r : ℕ) : ℝ)^k/(k.factorial : ℝ))*(1+(k : ℝ)/n)^k :=
        mul_le_mul_of_nonneg_right hchoose (by positivity)
      _ = (((n-r : ℕ) : ℝ)^k*(1+(k : ℝ)/n)^k)/(k.factorial : ℝ) := by ring
      _ ≤ ((n : ℝ)-(b : ℝ)*(k-1 : ℕ))^k/(k.factorial : ℝ) :=
        div_le_div_of_nonneg_right hpow hfact.le
      _ ≤ rank := hrank
  have hExp := power_exponential n k hn hkn
  have hExpComb : ((n-r).choose k : ℝ)*Real.exp ((k : ℝ)^2/(2*n)) ≤ rank :=
    (mul_le_mul_of_nonneg_left hExp (Nat.cast_nonneg _)).trans hcomb
  have hchoosePos : (0 : ℝ) < ((n-r).choose k : ℝ) := by exact_mod_cast Nat.choose_pos hknr
  change _ ≤ rank/(2*((n-r).choose k : ℝ))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*((n-r).choose k : ℝ))).mpr
  nlinarith

end SemAC02.Supplement.P2MBoundedCNFRankRatio
end

section
-- Inlined Solutions.P2MBoundedCNFDeterministicBound

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MBoundedCNFDeterministicBound

open MvPolynomial ACirc LiftSAParity P2MProofComplexity P2MExpansionCNFRepresentation

theorem lower {n : ℕ} {L : Type} [Fintype L] [DecidableEq L]
    (C : L → Clause (Fin n)) (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u))
    (hwidth : ∀ u, 2 ≤ (C u).card ∧ (C u).card ≤ 3)
    (d : ℕ) (hR : ∀ v, P2MCleaningDegreeReduction.rightDegree (representation C).graph v ≤ d)
    (s : ℝ) (hs : 1 ≤ s)
    (hstrict : ∀ J : Finset L, J.Nonempty → (J.card : ℝ) ≤ s →
      (J.card : ℝ)/2 < ((PCNonBool.boundaryOn (representation C).graph Finset.univ J).card : ℝ))
    (k : ℕ) (hk : 1 ≤ k) (hr3 : 3 ≤ (P2MBoundedOccurrenceRank.packingBound d+1)*k)
    (hbudgetN : 3*(k+(P2MBoundedOccurrenceRank.packingBound d+1)*k) ≤ n)
    (hbudgetS : (3*(k+(P2MBoundedOccurrenceRank.packingBound d+1)*k) : ℕ)+1 ≤ s/4)
    (π : List (ACirc (ZMod 2) (Fin n)))
    (hπ : IsSemPCRef IsSPS Set.univ (clauseAx (Set.range C)) π) :
    1/2*Real.exp ((k : ℝ)^2/(2*n)) ≤ topS Set.univ π := by
  let b := P2MBoundedOccurrenceRank.packingBound d
  let r := (b+1)*k
  let B := 3*(k+max 3 r)
  have hB : B = 3*(k+r) := by dsimp only [B]; rw [max_eq_right hr3]
  have hBN : B ≤ n := by rw [hB]; exact hbudgetN
  have hBS : (B : ℝ)+1 ≤ s/4 := by rw [hB]; exact hbudgetS
  have hkB : k ≤ B := by dsimp [B]; omega
  have hB3 : 3 ≤ B := by dsimp [B]; omega
  have hbk : b*(k-1) ≤ n := by
    have hh := Nat.mul_le_mul_left b (Nat.sub_le k 1)
    have hr : b*k ≤ r := by dsimp [r]; nlinarith
    dsimp [r] at *
    omega
  obtain ⟨R, hPseudo, hRank⟩ := P2MBoundedCNFOperatorWitness.exists_reduction C hC hwidth d hR
    s hs hstrict B k hB3 hBS hkB hbk
  have hF : ∀ p ∈ (representation C).axioms, AC02Frege.IsMultilinear p ∧ p.totalDegree ≤ 3 := by
    intro p hp
    exact ⟨multilinear C p hp, degrees C 3 (fun u => (hwidth u).2) p hp⟩
  have hπP : IsSemPCRef IsSPS Set.univ (polyAx (representation C).axioms) π := by
    rw [encoded_axioms]
    exact hπ
  have h44 := theorem_4_4_sps_size_bound (representation C).axioms 3 hF k r hk
    (hkB.trans hBN) (by dsimp [r]; omega) (by dsimp [r]; omega) hBN R hPseudo π hπP
  exact (P2MBoundedCNFRankRatio.lower n b k hk hbudgetN _ hRank).trans h44

end SemAC02.Supplement.P2MBoundedCNFDeterministicBound
end

section
-- Inlined Solutions.P2MCNFVariableEquivalence

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MCNFVariableEquivalence

open LiftSAParity P2MProofComplexity P2MExpansionCNFRepresentation

variable {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

def rename (e : V ≃ U) (C : Clause V) : Clause U :=
  C.map (e.prodCongr (Equiv.refl Bool)).toEmbedding

@[simp] theorem mem_rename (e : V ≃ U) (C : Clause V) (l : U × Bool) :
    l ∈ rename e C ↔ (e.symm l.1, l.2) ∈ C := by
  simp [rename, Finset.mem_map_equiv]
  rfl

@[simp] theorem card_rename (e : V ≃ U) (C : Clause V) : (rename e C).card = C.card := Finset.card_map _

theorem consistent (e : V ≃ U) (C : Clause V) (hC : P2MCNFExpansionPolynomials.Consistent C) :
    P2MCNFExpansionPolynomials.Consistent (rename e C) := by
  intro v ⟨hp, hn⟩
  exact hC (e.symm v) ⟨(mem_rename e C _).mp hp, (mem_rename e C _).mp hn⟩

theorem falsifies (e : V ≃ U) (C : Clause V) (y : U → Bool) :
    Falsifies y (rename e C) ↔ Falsifies (fun v => y (e v)) C := by
  constructor
  · intro hf l hl
    have hh := hf (e l.1, l.2) (by simpa only [mem_rename, Equiv.symm_apply_apply] using hl)
    exact hh
  · intro hf l hl
    have hh := hf (e.symm l.1, l.2) ((mem_rename e C l).mp hl)
    simpa only [Equiv.apply_symm_apply] using hh

variable {L : Type} [Fintype L] [DecidableEq L]

theorem graph_iff (e : V ≃ U) (C : L → Clause V)
    (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u)) (u : L) (v : U) :
    (representation (fun u => rename e (C u))).graph.Adj u v ↔
      (representation C).graph.Adj u (e.symm v) := by
  rw [P2MExpansionCNFRepresentation.graph_iff _ (fun u => consistent e (C u) (hC u)),
    P2MExpansionCNFRepresentation.graph_iff C hC]
  constructor
  · intro hv
    obtain ⟨⟨w, b⟩, hl, he⟩ := Finset.mem_image.mp hv
    dsimp only at he
    subst w
    exact Finset.mem_image.mpr ⟨(e.symm v, b), (mem_rename e _ _).mp hl, rfl⟩
  · intro hv
    obtain ⟨⟨w, b⟩, hl, he⟩ := Finset.mem_image.mp hv
    dsimp only at he
    subst w
    exact Finset.mem_image.mpr ⟨(v, b), (mem_rename e _ _).mpr hl, rfl⟩

theorem right_degree (e : V ≃ U) (C : L → Clause V)
    (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u)) (v : U) :
    P2MCleaningDegreeReduction.rightDegree (representation (fun u => rename e (C u))).graph v =
      P2MCleaningDegreeReduction.rightDegree (representation C).graph (e.symm v) := by
  unfold P2MCleaningDegreeReduction.rightDegree
  congr 1
  exact Finset.filter_congr (fun u hu => graph_iff e C hC u v)

theorem boundary_card (e : V ≃ U) (C : L → Clause V)
    (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u)) (J : Finset L) :
    (PCNonBool.boundaryOn (representation (fun u => rename e (C u))).graph Finset.univ J).card =
      (PCNonBool.boundaryOn (representation C).graph Finset.univ J).card := by
  classical
  have hf (v : U) : J.filter (fun u => (representation (fun u => rename e (C u))).graph.Adj u v) =
      J.filter (fun u => (representation C).graph.Adj u (e.symm v)) :=
    Finset.filter_congr (fun u hu => graph_iff e C hC u v)
  have he : (PCNonBool.boundaryOn (representation C).graph Finset.univ J).map e.toEmbedding =
      PCNonBool.boundaryOn (representation (fun u => rename e (C u))).graph Finset.univ J := by
    ext v
    simp only [Finset.mem_map_equiv, PCNonBool.boundaryOn, Finset.mem_filter,
      Finset.mem_univ, true_and, hf]
  have hh := congrArg Finset.card he
  simpa only [Finset.card_map] using hh.symm

theorem refutation (e : V ≃ U) (C : L → Clause V) (π : List (ACirc (ZMod 2) V))
    (hπ : IsSemPCRef ACirc.IsSPS Set.univ (clauseAx (Set.range C)) π) :
    IsSemPCRef ACirc.IsSPS Set.univ (clauseAx (Set.range (fun u => rename e (C u))))
      (π.map (P2MArithmeticLeafSubstitution.circuit (fun v => Sum.inl (e v)))) := by
  apply P2MSemanticLeafSubstitution.refutation (fun v => Sum.inl (e v)) _ _ _ _
    (P2MArithmeticLeafSubstitution.sps _) _ π hπ
  rintro a ⟨D, ⟨u, rfl⟩, rfl⟩
  left
  refine ⟨polyFn (clausePolyF (rename e (C u))),
    ⟨rename e (C u), ⟨u, rfl⟩, rfl⟩, ?_⟩
  intro y
  rw [P2MFieldSelectorClauseProjection.clause_value, P2MFieldSelectorClauseProjection.clause_value,
    falsifies]
  rfl

end SemAC02.Supplement.P2MCNFVariableEquivalence
end

section
-- Inlined Solutions.P2MRandomCNFLinearParameters

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MRandomCNFLinearParameters

noncomputable def fraction (γ : ℝ) (d : ℕ) : ℝ :=
  γ/(1000*((P2MBoundedOccurrenceRank.packingBound d : ℝ)+2))

theorem fraction_pos (γ : ℝ) (d : ℕ) (hγ : 0 < γ) : 0 < fraction γ d := by
  unfold fraction
  positivity

noncomputable def degree (γ : ℝ) (d n : ℕ) : ℕ := ⌊fraction γ d*n⌋₊

theorem budgets (γ : ℝ) (d n N : ℕ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 64 ≤ γ*n) (hdegree : 4 ≤ fraction γ d*n) (hN : (n : ℝ)/2 ≤ N) :
    1 ≤ degree γ d n ∧
    3 ≤ (P2MBoundedOccurrenceRank.packingBound d+1)*degree γ d n ∧
    3*(degree γ d n+(P2MBoundedOccurrenceRank.packingBound d+1)*degree γ d n) ≤ N ∧
    ((3*(degree γ d n+(P2MBoundedOccurrenceRank.packingBound d+1)*degree γ d n) : ℕ) : ℝ)+1 ≤ γ*n/8 ∧
    fraction γ d*n/2 ≤ degree γ d n := by
  let b := P2MBoundedOccurrenceRank.packingBound d
  let η := fraction γ d
  let k := degree γ d n
  have hη : 0 < η := fraction_pos γ d hγ
  have hn : (0 : ℝ) < n := by nlinarith
  have hfloor : (k : ℝ) ≤ η*n := Nat.floor_le (by positivity)
  have hceil : η*n < (k : ℝ)+1 := Nat.lt_floor_add_one _
  have hkR : (3 : ℝ) ≤ k := by linarith
  have hk : 3 ≤ k := by exact_mod_cast hkR
  have hprod : 3*((b : ℝ)+2)*(k : ℝ) ≤ 3*γ*n/1000 := by
    have hh := mul_le_mul_of_nonneg_left hfloor (show (0 : ℝ) ≤ 3*((b : ℝ)+2) by positivity)
    have he : 3*((b : ℝ)+2)*(η*n) = 3*γ*n/1000 := by
      dsimp [η, fraction, b]
      field_simp <;> ring
    rwa [he] at hh
  have hBReal : ((3*(k+(b+1)*k) : ℕ) : ℝ) ≤ 3*γ*n/1000 := by
    push_cast
    nlinarith [hprod]
  have hgn : γ*(n : ℝ) ≤ n := by nlinarith
  have hBN : 3*(k+(b+1)*k) ≤ N := by
    have hh : ((3*(k+(b+1)*k) : ℕ) : ℝ) ≤ N := by linarith
    exact_mod_cast hh
  refine ⟨by omega, ?_, hBN, ?_, ?_⟩
  · change 3 ≤ (b+1)*k
    have hh : k ≤ (b+1)*k := by nlinarith
    omega
  · linarith
  · linarith

theorem exponential (η : ℝ) (hη : 0 < η) (n N k : ℕ)
    (hN : 1 ≤ N) (hNn : N ≤ n) (hk : η*n/2 ≤ k) (hlarge : 32 ≤ η^2*n) :
    (2 : ℝ)^(η^2/32*n) ≤ 1/2*Real.exp ((k : ℝ)^2/(2*N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNnR : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hsq : (η*(n : ℝ)/2)^2 ≤ (k : ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) hk 2
  have hlow : η^2*n/8 ≤ (k : ℝ)^2/(2*N) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*N)).mpr
    have hh := mul_le_mul_of_nonneg_left hNnR (show (0 : ℝ) ≤ η^2*n by positivity)
    nlinarith
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexp : Real.log 2 + Real.log 2*(η^2/32*n) ≤ (k : ℝ)^2/(2*N) := by
    have hh := mul_le_mul_of_nonneg_right hlog (show (0 : ℝ) ≤ η^2/32*n by positivity)
    nlinarith
  have hh := Real.exp_le_exp.mpr hexp
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

end SemAC02.Supplement.P2MRandomCNFLinearParameters
end

section
-- Inlined Solutions.P2MArithmeticTopSize

namespace SemAC02.Supplement.P2MArithmeticTopSize

open ACirc P2MArithmeticCircuitBasics

theorem top_term_subterm {F V : Type} (c t : ACirc F V) (ht : t∈topTerms c) : t∈subterms c := by
  cases c with
  | var i => simp [topTerms] at ht
  | const a => simp [topTerms] at ht
  | prod cs => simp [topTerms] at ht
  | sum ps =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ht
    exact (mem_subterms_sum _ _).mpr (Or.inr ⟨p,hp,self_mem_subterms _⟩)

theorem top_le_csize {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    topS Ω π ≤ csize π := by
  classical
  let U := π.toFinset.biUnion subterms
  have hsub : P2MProofTopFunctions.pool Ω π⊆U.image (fun t => fun x : Ω => cval t x.1) := by
    intro g hg
    obtain ⟨hn,c,hc,t,ht,he⟩ := (P2MProofTopFunctions.mem_pool Ω π g).mp hg
    exact Finset.mem_image.mpr ⟨t,Finset.mem_biUnion.mpr
      ⟨c,List.mem_toFinset.mpr hc,top_term_subterm c t ht⟩,he⟩
  rw [←P2MProofTopFunctions.card_eq_topS]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end SemAC02.Supplement.P2MArithmeticTopSize
end

section
-- Inlined Solutions.P2MRandomThreeCNFDeterministicBound

set_option maxHeartbeats 4000000

namespace SemAC02.Supplement.P2MRandomThreeCNFDeterministicBound

open LiftSAParity ACirc P2MProofComplexity P2MExpansionCNFRepresentation P2MRandomCNFLinearParameters

theorem lower {n : ℕ} {L : Type} [Fintype L] [DecidableEq L]
    (C : L → Clause (Fin n)) (hC : ∀ u, P2MCNFExpansionPolynomials.Consistent (C u))
    (hwidth : ∀ u, (C u).card = 3) (α γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hm : (Fintype.card L : ℝ) ≤ α*n) (hlarge : 64 ≤ γ*n)
    (hdegree : 4 ≤ fraction γ (P2MRightDegreeReduction.degreeBound α γ)*n)
    (hexponent : 32 ≤ (fraction γ (P2MRightDegreeReduction.degreeBound α γ))^2*n)
    (hExp : P2MBipartiteNeighborhoodExpansion.Expands (representation C).graph (γ*n) (15/8))
    (π : List (ACirc (ZMod 2) (Fin n)))
    (hπ : IsSemPCRef IsSPS Set.univ (clauseAx (Set.range C)) π) :
    (2 : ℝ)^((fraction γ (P2MRightDegreeReduction.degreeBound α γ))^2/32*n) ≤ topS Set.univ π ∧
    (2 : ℝ)^((fraction γ (P2MRightDegreeReduction.degreeBound α γ))^2/32*n) ≤ csize π := by
  classical
  let d := P2MRightDegreeReduction.degreeBound α γ
  let η := fraction γ d
  let k := degree γ d n
  have hn : (0 : ℝ) < n := by nlinarith
  obtain ⟨I, A, z, hA, hz, hwidth', hR, hboundary⟩ :=
    P2MCNFCleaningFamilies.prepared_family C hC hwidth α γ hγ hγ1
      (by simpa only [Fintype.card_fin] using hm)
      (by simpa only [Fintype.card_fin] using hlarge)
      (by simpa only [Fintype.card_fin] using hExp)
  simp only [Fintype.card_fin] at hA hboundary
  let V := {v : Fin n // v ∉ A}
  let N := Fintype.card V
  have hNn : N ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun v : Fin n => v ∉ A)
  have hNcard : N = n-A.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_subtype_compl (fun v : Fin n => v ∈ A)
  have hAN : A.card ≤ n := by simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ A)
  have hNreal : (n : ℝ)/2 ≤ N := by
    have he : N + A.card = n := by omega
    have heR : (N : ℝ) + A.card = n := by exact_mod_cast he
    linarith
  have hN1 : 1 ≤ N := by
    have hh : (0 : ℝ) < N := by linarith
    exact_mod_cast hh
  let e : V ≃ Fin N := Fintype.equivFin V
  let C' := P2MCNFCleaningFamilies.family C I A
  let D := fun u => P2MCNFVariableEquivalence.rename e (C' u)
  have hC' := P2MCNFCleaningFamilies.family_consistent C hC I A
  have hD : ∀ u, P2MCNFExpansionPolynomials.Consistent (D u) :=
    fun u => P2MCNFVariableEquivalence.consistent e (C' u) (hC' u)
  have hDwidth : ∀ u, 2 ≤ (D u).card ∧ (D u).card ≤ 3 := by
    intro u
    simpa only [D, P2MCNFVariableEquivalence.card_rename] using hwidth' u
  have hDR : ∀ v, P2MCleaningDegreeReduction.rightDegree (representation D).graph v ≤ d := by
    intro v
    rw [P2MCNFVariableEquivalence.right_degree e C' hC' v]
    exact hR (e.symm v)
  have hDstrict : ∀ J, J.Nonempty → (J.card : ℝ) ≤ γ*n/2 →
      (J.card : ℝ)/2 < ((PCNonBool.boundaryOn (representation D).graph Finset.univ J).card : ℝ) := by
    intro J hJ hJs
    rw [P2MCNFVariableEquivalence.boundary_card e C' hC' J]
    exact hboundary J hJ hJs
  let π' := π.map (P2MArithmeticLeafSubstitution.circuit (P2MCNFPartialRestriction.substitution A z))
  let π'' := π'.map (P2MArithmeticLeafSubstitution.circuit (fun v => Sum.inl (e v)))
  have hπ' := P2MCNFCleaningFamilies.refutation C I A z hz π hπ
  have hπ'' := P2MCNFVariableEquivalence.refutation e C' π' hπ'
  obtain ⟨hk, hr3, hbudgetN, hbudgetS, hkLower⟩ := budgets γ d n N hγ hγ1 hlarge hdegree hNreal
  have hLower := P2MBoundedCNFDeterministicBound.lower D hD hDwidth d hDR (γ*n/2)
    (by linarith) hDstrict k hk hr3 hbudgetN (by convert hbudgetS using 1 <;> ring) π'' hπ''
  have hNumeric := exponential η (fraction_pos γ d hγ) n N k hN1 hNn hkLower hexponent
  have hTop : topS Set.univ π'' ≤ topS Set.univ π :=
    (P2MArithmeticLeafSubstitution.top_bound (fun v => Sum.inl (e v)) π').trans
      (P2MArithmeticLeafSubstitution.top_bound (P2MCNFPartialRestriction.substitution A z) π)
  have hFinal := (hNumeric.trans hLower).trans (by exact_mod_cast hTop :
    (topS Set.univ π'' : ℝ) ≤ topS Set.univ π)
  exact ⟨hFinal, hFinal.trans (by exact_mod_cast P2MArithmeticTopSize.top_le_csize Set.univ π)⟩

end SemAC02.Supplement.P2MRandomThreeCNFDeterministicBound
end

section
-- Inlined Solutions.P2MBinomialExponentialUpperBound

set_option maxHeartbeats 1000000

namespace P2MProofComplexity.P2MBinomialExponentialUpperBound

theorem factorial_lower (k : ℕ) : ((k : ℝ)/Real.exp 1)^k ≤ (k.factorial : ℝ) := by
  by_cases hk : k=0
  · subst k; simp
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2*Real.pi*k) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  exact (le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ ((k : ℝ)/Real.exp 1)^k) hsqrt).trans
    (Stirling.le_factorial_stirling k)

theorem choose_upper (n k : ℕ) : (n.choose k : ℝ) ≤ (Real.exp 1*n/k)^k := by
  by_cases hk : k=0
  · subst k; simp
  have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0 < k by omega)
  have he : (0 : ℝ)<Real.exp 1 := Real.exp_pos _
  calc
    (n.choose k : ℝ) ≤ (n : ℝ)^k/(k.factorial : ℝ) := Nat.choose_le_pow_div k n
    _ ≤ (n : ℝ)^k/((k : ℝ)/Real.exp 1)^k :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (div_pos hkR he) k) (factorial_lower k)
    _ = _ := by rw [←div_pow]; congr 1; field_simp

end P2MProofComplexity.P2MBinomialExponentialUpperBound
end

section
-- Inlined Solutions.P2MNeighborhoodEntropyBound

set_option maxHeartbeats 1000000

namespace P2MProofComplexity.P2MNeighborhoodEntropyBound

theorem monotone_rounding (n a u v : ℝ) (hn : 0 < n) (hu : 0 < u)
    (huv : u ≤ v) (hvn : v ≤ n) (hua : u ≤ a) :
    u+(a-u)*Real.log (u/n) ≤ v+(a-v)*Real.log (v/n) := by
  have hv : 0 < v := hu.trans_le huv
  have hlog : Real.log (u/n) ≤ Real.log (v/n) :=
    Real.log_le_log (div_pos hu hn) (div_le_div_of_nonneg_right huv hn.le)
  have hln : Real.log (v/n) ≤ 0 := Real.log_nonpos (div_nonneg hv.le hn.le) ((div_le_one hn).mpr hvn)
  calc
    u+(a-u)*Real.log (u/n) ≤ u+(a-u)*Real.log (v/n) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hua)) u
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr huv) (neg_nonneg.mpr hln)]

theorem binomial_containment (n u b : ℕ) (hn : 0 < n) (hu : 0 < u) :
    (n.choose u : ℝ)*((u : ℝ)/n)^b ≤
      Real.exp ((u : ℝ)+((b : ℝ)-u)*Real.log ((u : ℝ)/n)) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have huR : (0 : ℝ)<u := by exact_mod_cast hu
  apply (mul_le_mul_of_nonneg_right (P2MBinomialExponentialUpperBound.choose_upper n u) (by positivity)).trans
  have hpos : 0 < Real.exp 1*(n : ℝ)/u := by positivity
  have hA : (Real.exp 1*(n : ℝ)/u)^u=Real.exp ((u : ℝ)*(1-Real.log ((u : ℝ)/n))) := by
    rw [Real.exp_nat_mul,←Real.exp_log hpos]
    congr 1
    rw [Real.log_div (by positivity) huR.ne',Real.log_mul (Real.exp_pos _).ne' hnR.ne',Real.log_exp,
      Real.log_div huR.ne' hnR.ne']
    ring
  have hB : ((u : ℝ)/n)^b=Real.exp ((b : ℝ)*Real.log ((u : ℝ)/n)) := by
    rw [Real.exp_nat_mul,Real.exp_log (div_pos huR hnR)]
  rw [hA,hB,←Real.exp_add]
  apply le_of_eq
  congr 1
  ring

theorem binomial_pair (m n t u w : ℕ) (hm : 0 < m) (hn : 0 < n) (ht : 0 < t) (hu : 0 < u) :
    (m.choose t : ℝ)*(n.choose u : ℝ)*((u : ℝ)/n)^(w*t) ≤
      Real.exp ((t : ℝ)*(1+Real.log ((m : ℝ)/t))+
        (u : ℝ)+((w : ℝ)*t-u)*Real.log ((u : ℝ)/n)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have hb := binomial_containment n u (w*t) hn hu
  have he : (Real.exp 1*(m : ℝ)/t)^t=Real.exp ((t : ℝ)*(1+Real.log ((m : ℝ)/t))) := by
    rw [Real.exp_nat_mul,←Real.exp_log (by positivity : 0 < Real.exp 1*(m : ℝ)/t)]
    congr 1
    rw [Real.log_div (by positivity) htR.ne',Real.log_mul (Real.exp_pos _).ne' hmR.ne',Real.log_exp,
      Real.log_div hmR.ne' htR.ne']
    ring
  calc
    _ = (m.choose t : ℝ)*((n.choose u : ℝ)*((u : ℝ)/n)^(w*t)) := by ring
    _ ≤ (Real.exp 1*(m : ℝ)/t)^t*Real.exp ((u : ℝ)+(((w*t : ℕ) : ℝ)-u)*Real.log ((u : ℝ)/n)) :=
      mul_le_mul (P2MBinomialExponentialUpperBound.choose_upper m t) hb (by positivity) (by positivity)
    _ = _ := by rw [he,←Real.exp_add]; push_cast; congr 1; ring

end P2MProofComplexity.P2MNeighborhoodEntropyBound
end

section
-- Inlined Solutions.P2MRandomThreeCNFEntropy

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MRandomThreeCNFEntropy

open P2MProofComplexity.P2MNeighborhoodEntropyBound

noncomputable def budget (α : ℝ) : ℝ := 5+|Real.log α|
noncomputable def expansionFraction (α : ℝ) : ℝ := Real.exp (-16*budget α)

 theorem fraction_bounds (α : ℝ) : 0 < expansionFraction α ∧ expansionFraction α ≤ 1/2 := by
  refine ⟨Real.exp_pos _,?_⟩
  have hB : 5 ≤ budget α := by dsimp [budget]; linarith [abs_nonneg (Real.log α)]
  have hh := Real.add_one_le_exp (16*budget α)
  unfold expansionFraction
  rw [show -16*budget α= -(16*budget α) by ring,Real.exp_neg,←one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith)

 theorem exponent_bound (α n m t u : ℝ) (hα : 0 < α) (hn : 0 < n) (hm : 0 < m)
    (ht : 1 ≤ t) (hu : 0 < u) (hum : u ≤ 15*t/8) (hmα : m ≤ α*n)
    (htn : t/n ≤ expansionFraction α) :
    t*(1+Real.log (m/t))+u+(3*t-u)*Real.log (u/n) ≤ -Real.log n/16-(t-1) := by
  have ht0 : 0 < t := by linarith
  have hB : 5 ≤ budget α := by dsimp [budget]; linarith [abs_nonneg (Real.log α)]
  have hRatio : 0 < t/n := div_pos ht0 hn
  have hHalf : t/n ≤ 1/2 := htn.trans (fraction_bounds α).2
  have htn' : t ≤ n/2 := by have hh := (div_le_iff₀ hn).mp hHalf; linarith
  let l := Real.log (t/n)
  have hl : l ≤ -16*budget α := (Real.log_le_log hRatio htn).trans_eq (Real.log_exp _)
  have hRound := monotone_rounding n (3*t) u (15*t/8) hn hu hum (by linarith) (by linarith)
  have hLogV : Real.log ((15*t/8)/n) ≤ Real.log 2+l := by
    apply (Real.log_le_log (by positivity : 0 < (15*t/8)/n)
      (div_le_div_of_nonneg_right (by linarith : 15*t/8 ≤ 2*t) hn.le)).trans_eq
    rw [show (2*t)/n=2*(t/n) by ring,Real.log_mul (by norm_num) hRatio.ne']
  have hLast : u+(3*t-u)*Real.log (u/n) ≤ 15*t/8+(9*t/8)*(Real.log 2+l) := by
    apply hRound.trans
    have hh := mul_le_mul_of_nonneg_left hLogV (show 0 ≤ 3*t-15*t/8 by linarith)
    nlinarith
  have hLogM : Real.log (m/t) ≤ Real.log α-l := by
    apply (Real.log_le_log (div_pos hm ht0) (div_le_div_of_nonneg_right hmα ht0.le)).trans_eq
    dsimp only [l]
    rw [Real.log_div (mul_pos hα hn).ne' ht0.ne',Real.log_mul hα.ne' hn.ne',
      Real.log_div ht0.ne' hn.ne']
    ring
  have hLog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hConstant : 23/8+Real.log α+(9/8)*Real.log 2 ≤ budget α := by
    have hh := le_abs_self (Real.log α)
    dsimp [budget]
    linarith
  have hNormalized : t*(1+Real.log (m/t))+u+(3*t-u)*Real.log (u/n) ≤ t*(budget α+l/8) := by
    have hFirst := mul_le_mul_of_nonneg_left hLogM ht0.le
    have hC := mul_le_mul_of_nonneg_left hConstant ht0.le
    nlinarith
  have hNorm : t*(budget α+l/8) ≤ t*l/16 := by
    have hh := mul_le_mul_of_nonneg_left hl ht0.le
    nlinarith
  have hlSplit : l=Real.log t-Real.log n := Real.log_div ht0.ne' hn.ne'
  have hTail := mul_le_mul_of_nonneg_left hl (show 0 ≤ (t-1)/16 by linarith)
  have hLogT := Real.log_le_sub_one_of_pos ht0
  have hEnd : t*l/16 ≤ -Real.log n/16-(t-1) := by
    have he : t*l/16=(Real.log t-Real.log n)/16+((t-1)/16)*l := by rw [←hlSplit]; ring
    rw [he]
    nlinarith [mul_nonneg (show 0 ≤ t-1 by linarith) (show 0 ≤ budget α-17/16 by linarith)]
  exact hNormalized.trans (hNorm.trans hEnd)

 theorem union_term (α : ℝ) (hα : 0 < α) (n m t u : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (ht : 1 ≤ t) (hu : 1 ≤ u) (hum : (u : ℝ) ≤ 15*(t : ℝ)/8) (hmα : (m : ℝ) ≤ α*n)
    (htn : (t : ℝ)/n ≤ expansionFraction α) :
    (m.choose t : ℝ)*(n.choose u : ℝ)*((u : ℝ)/n)^(3*t) ≤
      Real.exp (-Real.log n/16-((t : ℝ)-1)) := by
  apply (binomial_pair m n t u 3 (by omega) (by omega) (by omega) (by omega)).trans
  apply Real.exp_le_exp.mpr
  simpa only [Nat.cast_ofNat] using exponent_bound α n m t u hα
    (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast (show 0 < m by omega))
    (by exact_mod_cast ht) (by exact_mod_cast (show 0 < u by omega)) hum hmα htn

end SemAC02.Supplement.P2MRandomThreeCNFEntropy
end

section
-- Inlined Solutions.P2MWidthClauseEncoding

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MWidthClauseEncoding

open LiftSAParity

abbrev VarSet (n w : ℕ) := {S : Finset (Fin n) // S.card=w}
abbrev SignedSet (n w : ℕ) := (S : VarSet n w) × (S.1 → Bool)

noncomputable def encode {n : ℕ} (S : Finset (Fin n)) (b : S → Bool) : Clause (Fin n) :=
  Finset.univ.image (fun x : S => (x.1,b x))

theorem encode_card {n : ℕ} (S : Finset (Fin n)) (b : S → Bool) : (encode S b).card=S.card := by
  rw [encode,Finset.card_image_of_injective,Finset.card_univ,Fintype.card_coe]
  intro x y h
  exact Subtype.ext (congrArg Prod.fst h)

theorem encode_vars {n : ℕ} (S : Finset (Fin n)) (b : S → Bool) : (encode S b).image Prod.fst=S := by
  ext i
  simp only [encode,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨l,⟨x,rfl⟩,rfl⟩
    exact x.2
  · intro hi
    exact ⟨(i,b ⟨i,hi⟩),⟨⟨i,hi⟩,rfl⟩,rfl⟩

noncomputable def pack {n w : ℕ} (z : SignedSet n w) : WClause n w :=
  ⟨encode z.1.1 z.2,(encode_card _ _).trans z.1.2,by rw [encode_vars]; exact z.1.2⟩

theorem encode_injective {n : ℕ} (S : Finset (Fin n)) (b c : S → Bool)
    (he : encode S b=encode S c) : b=c := by
  funext x
  have hx : (x.1,b x)∈encode S c := by
    rw [←he]
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hx
  have hyx : y=x := Subtype.ext (congrArg Prod.fst hxy)
  subst y
  exact (congrArg Prod.snd hxy).symm

theorem pack_injective {n w : ℕ} : Function.Injective (pack : SignedSet n w → WClause n w) := by
  intro z z' he
  rcases z with ⟨S,b⟩
  rcases z' with ⟨T,c⟩
  have henc : encode S.1 b=encode T.1 c := congrArg Subtype.val he
  have hST : S=T := Subtype.ext (by
    have hv := congrArg (Finset.image Prod.fst) henc
    simpa only [encode_vars] using hv)
  subst T
  have hbc := encode_injective S.1 b c henc
  subst c
  rfl

noncomputable def labels {n w : ℕ} (C : WClause n w) (x : (C.1.image Prod.fst)) : Bool :=
  decide ((x.1,true)∈C.1)

theorem labels_eq {n w : ℕ} (C : WClause n w) (i : Fin n) (b : Bool) (hl : (i,b)∈C.1) :
    labels C ⟨i,Finset.mem_image.mpr ⟨(i,b),hl,rfl⟩⟩=b := by
  cases b
  · have hnot : (i,true)∉C.1 := fun h => P2MCNFExpansionPolynomials.wclause_consistent C i ⟨h,hl⟩
    simp [labels,hnot]
  · simp [labels,hl]

theorem pack_surjective {n w : ℕ} : Function.Surjective (pack : SignedSet n w → WClause n w) := by
  intro C
  refine ⟨⟨⟨C.1.image Prod.fst,C.2.2⟩,labels C⟩,?_⟩
  apply Subtype.ext
  ext l
  constructor
  · intro hl
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hl
    by_cases hb : labels C x=true
    · simpa only [hb] using (of_decide_eq_true hb : (x.1,true)∈C.1)
    · have hf : labels C x=false := Bool.eq_false_iff.mpr hb
      obtain ⟨⟨i,b⟩,hl,he⟩ := Finset.mem_image.mp x.2
      have he' : i=x.1 := he
      subst i
      have hlabel := labels_eq C x.1 b hl
      have hb' : b=labels C x := hlabel.symm
      simpa only [hb'] using hl
  · intro hl
    refine Finset.mem_image.mpr ⟨⟨l.1,Finset.mem_image.mpr ⟨l,hl,rfl⟩⟩,Finset.mem_univ _,?_⟩
    exact Prod.ext rfl (labels_eq C l.1 l.2 hl)

noncomputable def equivalence (n w : ℕ) : SignedSet n w ≃ WClause n w :=
  Equiv.ofBijective pack ⟨pack_injective,pack_surjective⟩

theorem card (n w : ℕ) : Fintype.card (WClause n w)=n.choose w*2^w := by
  classical
  rw [←Fintype.card_congr (equivalence n w),Fintype.card_sigma]
  have hc (S : VarSet n w) : Fintype.card (S.1 → Bool)=2^w := by
    rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,S.2]
  simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  congr 1
  have he : Finset.univ.filter (fun S : Finset (Fin n) => S.card=w)=
      (Finset.univ : Finset (Fin n)).powersetCard w := by ext S; simp
  rw [Fintype.card_subtype,he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

end SemAC02.Supplement.P2MWidthClauseEncoding
end

section
-- Inlined Solutions.P2MUniformFiniteProbability

set_option maxHeartbeats 1000000

namespace P2MProofComplexity.P2MUniformFiniteProbability

open SemAC02.Supplement

attribute [local instance] Classical.propDecidable

theorem nonneg {A : Type} [Fintype A] (E : A → Prop) : 0 ≤ uprob E := by unfold uprob; positivity

theorem le_one {A : Type} [Fintype A] (E : A → Prop) : uprob E ≤ 1 := by
  classical
  unfold uprob
  apply div_le_one_of_le₀
  · exact_mod_cast (Finset.card_le_univ (Finset.univ.filter E))
  · positivity

theorem mono {A : Type} [Fintype A] (E F : A → Prop) (h : ∀ a, E a → F a) : uprob E ≤ uprob F := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hs : Finset.univ.filter E⊆Finset.univ.filter F := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h a (Finset.mem_filter.mp ha).2⟩
  exact_mod_cast Finset.card_le_card hs

theorem complement {A : Type} [Fintype A] [Nonempty A] (E : A → Prop) :
    uprob (fun a => ¬ E a)=1-uprob E := by
  classical
  have hc : ((Finset.univ.filter (fun a => ¬ E a)).card : ℝ)+
      ((Finset.univ.filter E).card : ℝ)=Fintype.card A := by
    have hh := Finset.card_filter_add_card_filter_not (s:=Finset.univ) E
    have hn : (Finset.univ.filter (fun a => ¬ E a)).card+(Finset.univ.filter E).card=Fintype.card A := by
      simpa only [Finset.card_univ,Nat.add_comm] using hh
    exact_mod_cast hn
  have hn : (Fintype.card A : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold uprob
  apply (eq_sub_iff_add_eq).mpr
  rw [Finset.filter_congr_decidable Finset.univ (fun a => ¬ E a) (Classical.decPred _)]
  rw [←add_div,hc,div_self hn]

theorem union_bound {A I : Type} [Fintype A] (S : Finset I) (E : A → Prop) (F : I → A → Prop)
    (h : ∀ a, E a → ∃ i∈S, F i a) : uprob E ≤ ∑ i∈S, uprob (F i) := by
  classical
  have hsub : Finset.univ.filter E⊆S.biUnion (fun i => Finset.univ.filter (F i)) := by
    intro a ha
    obtain ⟨i,hi,hFi⟩ := h a (Finset.mem_filter.mp ha).2
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hFi⟩⟩
  have hc : ((Finset.univ.filter E).card : ℝ) ≤ ∑ i∈S, ((Finset.univ.filter (F i)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  unfold uprob
  rw [←Finset.sum_div]
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

noncomputable def productEventEquiv {A I : Type} (E : I → A → Prop) :
    {f : I → A // ∀ i, E i (f i)} ≃ ((i : I) → {a : A // E i a}) where
  toFun f i := ⟨f.1 i,f.2 i⟩
  invFun f := ⟨fun i => (f i).1,fun i => (f i).2⟩
  left_inv f := rfl
  right_inv f := rfl

theorem independent {A I : Type} [Fintype A] [Fintype I] [DecidableEq I] (E : I → A → Prop) :
    uprob (fun f : I → A => ∀ i, E i (f i))=∏ i, uprob (E i) := by
  classical
  have hc : ((Finset.univ.filter (fun f : I → A => ∀ i, E i (f i))).card : ℝ)=
      ∏ i, ((Finset.univ.filter (E i)).card : ℝ) := by
    rw [←Fintype.card_subtype,Fintype.card_congr (productEventEquiv E),Fintype.card_pi]
    simp only [Nat.cast_prod,Fintype.card_subtype]
  unfold uprob
  rw [Finset.filter_congr_decidable Finset.univ (fun f : I → A => ∀ i, E i (f i)) (Classical.decPred _)]
  rw [hc,Finset.prod_div_distrib]
  congr 1
  simp

theorem congr {A : Type} [Fintype A] (E F : A → Prop) (h : ∀ a, E a ↔ F a) : uprob E=uprob F :=
  le_antisymm (mono E F (fun a => (h a).mp)) (mono F E (fun a => (h a).mpr))

theorem true_event {A : Type} [Fintype A] [Nonempty A] : uprob (fun _ : A => True)=1 := by
  simp [uprob,Fintype.card_ne_zero]

theorem equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (E : B → Prop) :
    uprob (fun a => E (e a))=uprob E := by
  classical
  unfold uprob
  rw [Fintype.card_congr e]
  congr 1
  apply congrArg Nat.cast
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb he
    exact e.injective he
  · intro b hb
    exact ⟨e.symm b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using (Finset.mem_filter.mp hb).2⟩,e.apply_symm_apply b⟩

theorem coordinates {A I : Type} [Fintype A] [Nonempty A] [Fintype I] [DecidableEq I]
    (J : Finset I) (E : A → Prop) :
    uprob (fun f : I → A => ∀ i∈J, E (f i))=(uprob E)^J.card := by
  classical
  rw [independent (fun i a => i∈J → E a)]
  have he (i : I) : uprob (fun a => i∈J → E a)=if i∈J then uprob E else 1 := by
    by_cases hi : i∈J
    · rw [if_pos hi]
      exact congr _ _ (fun a => by simp [hi])
    · rw [if_neg hi]
      exact (congr _ _ (fun a => by simp [hi])).trans true_event
  simp only [he]
  rw [←Finset.prod_filter]
  have hfilter : (Finset.univ : Finset I).filter (· ∈ J)=J := by ext i; simp
  rw [hfilter,Finset.prod_const]

theorem intersection_lower {A : Type} [Fintype A] [Nonempty A] (E F : A → Prop) :
    uprob E+uprob F-1 ≤ uprob (fun a => E a ∧ F a) := by
  classical
  have hb := union_bound (Finset.univ : Finset Bool) (fun a => ¬ (E a ∧ F a))
    (fun b a => if b then ¬ E a else ¬ F a) (by
      intro a ha
      by_cases he : E a
      · exact ⟨false,Finset.mem_univ _,by simpa using (fun hf => ha ⟨he,hf⟩)⟩
      · exact ⟨true,Finset.mem_univ _,by simpa using he⟩)
  have hh : uprob (fun a => ¬ (E a ∧ F a)) ≤ uprob (fun a => ¬ E a)+uprob (fun a => ¬ F a) := by
    simpa [Bool.forall_bool,add_comm] using hb
  rw [complement,complement,complement] at hh
  linarith

end P2MProofComplexity.P2MUniformFiniteProbability
end

section
-- Inlined Solutions.P2MSamplingJointProbabilities

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MSamplingJointProbabilities

theorem choose_power_compare (N j k : ℕ) (hj : j ≤ N) :
    j.choose k*N^k ≤ N.choose k*j^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k+1 ≤ j
    · have hratio : (j-k)*N ≤ (N-k)*j := by
        rw [Nat.sub_mul,Nat.sub_mul,Nat.mul_comm N j]
        exact Nat.sub_le_sub_left (Nat.mul_le_mul_left k hj) _
      apply Nat.le_of_mul_le_mul_right (c:=k+1) ?_ (by omega)
      calc
        _ = (j.choose (k+1)*(k+1))*N^k*N := by rw [pow_succ]; ring
        _ = (j.choose k*(j-k))*N^k*N := by rw [Nat.choose_succ_right_eq]
        _ = (j.choose k*N^k)*((j-k)*N) := by ring
        _ ≤ (N.choose k*j^k)*((j-k)*N) := Nat.mul_le_mul_right _ ih
        _ ≤ (N.choose k*j^k)*((N-k)*j) := Nat.mul_le_mul_left _ hratio
        _ = (N.choose k*(N-k))*j^k*j := by ring
        _ = (N.choose (k+1)*(k+1))*j^k*j := by rw [Nat.choose_succ_right_eq]
        _ = (N.choose (k+1)*j^(k+1))*(k+1) := by rw [pow_succ]; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : j < k+1)]
      simp

theorem choose_ratio_le (N j k : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (hk : k ≤ N) :
    (j.choose k : ℝ)/(N.choose k : ℝ) ≤ ((j : ℝ)/(N : ℝ))^k := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hC : 0 < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  rw [div_pow]
  apply (div_le_div_iff₀ hC (pow_pos hNp k)).mpr
  have h := choose_power_compare N j k hj
  have hh : (j.choose k : ℝ)*(N : ℝ)^k ≤ (N.choose k : ℝ)*(j : ℝ)^k := by exact_mod_cast h
  nlinarith

theorem joint_bound (N j : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (A : Finset (Fin N)) :
    ((((Finset.univ : Finset (Fin N)).powersetCard j).filter (A ⊆ ·)).card : ℝ)/
      (N.choose j : ℝ) ≤ ((j : ℝ)/(N : ℝ))^A.card := by
  classical
  have hAN : A.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ A
  by_cases hAj : A.card ≤ j
  · rw [Finset.card_filter_powersetCard_subset A Finset.univ j (Finset.subset_univ _) hAj,
      Finset.card_univ,Fintype.card_fin]
    have hCNj : 0 < (N.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
    have hCNk : 0 < (N.choose A.card : ℝ) := by exact_mod_cast Nat.choose_pos hAN
    have he : ((N-A.card).choose (j-A.card) : ℝ)/(N.choose j : ℝ) =
        (j.choose A.card : ℝ)/(N.choose A.card : ℝ) := by
      apply (div_eq_div_iff hCNj.ne' hCNk.ne').mpr
      have h := Nat.choose_mul (n:=N) hAj
      have hh : (N.choose j : ℝ)*(j.choose A.card : ℝ) =
          (N.choose A.card : ℝ)*((N-A.card).choose (j-A.card) : ℝ) := by exact_mod_cast h
      nlinarith
    rw [he]
    exact choose_ratio_le N j A.card hN hj hAN
  · have he : ((Finset.univ : Finset (Fin N)).powersetCard j).filter (A ⊆ ·) = ∅ := by
      apply Finset.ext
      intro S
      constructor
      · intro hS
        exfalso
        obtain ⟨hSj,hAS⟩ := Finset.mem_filter.mp hS
        have hcard := (Finset.mem_powersetCard.mp hSj).2
        have hh := Finset.card_le_card hAS
        omega
      · simp
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,zero_div]
    positivity

end AC02Frege.P2MSamplingJointProbabilities
end

section
-- Inlined Solutions.P2MUniformSubsetContainment

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MUniformSubsetContainment

open AC02Frege.P2MSamplingJointProbabilities

theorem probability {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hN : 1 ≤ Fintype.card V) (hk : k ≤ Fintype.card V) (A : Finset V) :
    ((((Finset.univ : Finset V).powersetCard k).filter (A ⊆ ·)).card : ℝ)/
      ((Fintype.card V).choose k : ℝ) ≤ ((k : ℝ)/(Fintype.card V : ℝ))^A.card := by
  classical
  let N := Fintype.card V
  have hAN : A.card ≤ N := Finset.card_le_univ A
  by_cases hAk : A.card ≤ k
  · rw [Finset.card_filter_powersetCard_subset A Finset.univ k (Finset.subset_univ _) hAk,Finset.card_univ]
    have hCNk : 0 < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
    have hCNA : 0 < (N.choose A.card : ℝ) := by exact_mod_cast Nat.choose_pos hAN
    have he : ((N-A.card).choose (k-A.card) : ℝ)/(N.choose k : ℝ)=
        (k.choose A.card : ℝ)/(N.choose A.card : ℝ) := by
      apply (div_eq_div_iff hCNk.ne' hCNA.ne').mpr
      have h := Nat.choose_mul (n:=N) hAk
      have hh : (N.choose k : ℝ)*(k.choose A.card : ℝ)=
          (N.choose A.card : ℝ)*((N-A.card).choose (k-A.card) : ℝ) := by exact_mod_cast h
      nlinarith
    rw [he]
    exact choose_ratio_le N k A.card hN hk hAN
  · have he : ((Finset.univ : Finset V).powersetCard k).filter (A ⊆ ·)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      obtain ⟨hSk,hAS⟩ := Finset.mem_filter.mp hS
      have hcard := (Finset.mem_powersetCard.mp hSk).2
      have hh := Finset.card_le_card hAS
      omega
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,zero_div]
    positivity


theorem probability_rpow {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) (A : Finset V)
    (b : ℝ) (hb : b ≤ (A.card : ℝ)) :
    ((((Finset.univ : Finset V).powersetCard k).filter (A ⊆ ·)).card : ℝ)/
      ((Fintype.card V).choose k : ℝ) ≤ ((k : ℝ)/(Fintype.card V : ℝ))^b := by
  have hN : 1 ≤ Fintype.card V := hk.trans hkn
  have hNpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hp : (0 : ℝ) < (k : ℝ)/(Fintype.card V : ℝ) :=
    div_pos (by exact_mod_cast (show 0 < k by omega)) hNpos
  have hp1 : (k : ℝ)/(Fintype.card V : ℝ) ≤ 1 :=
    (div_le_one hNpos).mpr (by exact_mod_cast hkn)
  apply (probability k hN hkn A).trans
  rw [←Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hp hp1 hb

end P2MProofComplexity.P2MUniformSubsetContainment
end

section
-- Inlined Solutions.P2MWidthClauseCounts

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MWidthClauseCounts

open LiftSAParity P2MWidthClauseEncoding P2MProofComplexity.P2MUniformFiniteProbability

attribute [local instance] Classical.propDecidable

def variableSet {n w : ℕ} (C : WClause n w) : VarSet n w := ⟨C.1.image Prod.fst,C.2.2⟩

theorem variableSet_pack {n w : ℕ} (z : SignedSet n w) : variableSet (pack z)=z.1 :=
  Subtype.ext (encode_vars z.1.1 z.2)

theorem varSet_card (n w : ℕ) : Fintype.card (VarSet n w)=n.choose w := by
  classical
  have he : Finset.univ.filter (fun S : Finset (Fin n) => S.card=w)=
      (Finset.univ : Finset (Fin n)).powersetCard w := by ext S; simp
  rw [Fintype.card_subtype,he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

theorem fiber_count {n w : ℕ} (E : VarSet n w → Prop) :
    Fintype.card {C : WClause n w // E (variableSet C)}=
      Fintype.card {S : VarSet n w // E S}*2^w := by
  classical
  let e : {z : SignedSet n w // E z.1} ≃ {C : WClause n w // E (variableSet C)} :=
    (equivalence n w).subtypeEquiv (fun z => by change E z.1 ↔ E (variableSet (pack z)); rw [variableSet_pack])
  rw [←Fintype.card_congr e,Fintype.card_congr (Equiv.subtypeSigmaEquiv (fun S : VarSet n w => S.1 → Bool) E),
    Fintype.card_sigma]
  have hc (S : {S : VarSet n w // E S}) : Fintype.card (S.1.1 → Bool)=2^w := by
    rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,S.1.2]
  simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul]

theorem contained_sets {n w : ℕ} (A : Finset (Fin n)) :
    Fintype.card {S : VarSet n w // S.1⊆A}=A.card.choose w := by
  classical
  let e : {S : VarSet n w // S.1⊆A} ≃ {S : Finset (Fin n) // S∈A.powersetCard w} := {
    toFun S := ⟨S.1.1,Finset.mem_powersetCard.mpr ⟨S.2,S.1.2⟩⟩
    invFun S := ⟨⟨S.1,(Finset.mem_powersetCard.mp S.2).2⟩,(Finset.mem_powersetCard.mp S.2).1⟩
    left_inv S := rfl
    right_inv S := rfl }
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powersetCard]

theorem contained_clauses {n w : ℕ} (A : Finset (Fin n)) :
    Fintype.card {C : WClause n w // C.1.image Prod.fst⊆A}=A.card.choose w*2^w := by
  change Fintype.card {C : WClause n w // (variableSet C).1⊆A}=_
  have hh := fiber_count (n:=n) (w:=w) (fun S => S.1⊆A)
  convert hh using 1
  · exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
  · congr 1
    exact (contained_sets A).symm.trans (congrArg (@Fintype.card _) (Subsingleton.elim _ _))

theorem contained_probability {n w : ℕ} (hw : w ≤ n) (A : Finset (Fin n)) :
    uprob (fun C : WClause n w => C.1.image Prod.fst⊆A)=
      (A.card.choose w : ℝ)/(n.choose w : ℝ) := by
  classical
  unfold uprob
  rw [←Fintype.card_subtype,contained_clauses,P2MWidthClauseEncoding.card]
  push_cast
  exact mul_div_mul_right _ _ (by positivity : (2 : ℝ)^w≠0)

theorem contained_probability_bound {n w : ℕ} (hn : 1 ≤ n) (hw : w ≤ n) (A : Finset (Fin n)) :
    uprob (fun C : WClause n w => C.1.image Prod.fst⊆A) ≤ ((A.card : ℝ)/(n : ℝ))^w := by
  rw [contained_probability hw A]
  exact AC02Frege.P2MSamplingJointProbabilities.choose_ratio_le n A.card w hn (by simpa using Finset.card_le_univ A) hw

theorem falsifies_encode {n : ℕ} (y : Fin n → Bool) (S : Finset (Fin n)) (b : S → Bool) :
    Falsifies y (encode S b) ↔ b=(fun x => !(y x.1)) := by
  constructor
  · intro hf
    funext x
    have hh := hf (x.1,b x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
    cases hy : y x.1 <;> cases hb : b x <;> simp_all
  · rintro rfl l hl
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hl
    simp

noncomputable def fixedSignsEquiv {n w : ℕ} (y : Fin n → Bool) :
    {z : SignedSet n w // z.2=(fun x => !(y x.1))} ≃ VarSet n w where
  toFun z := z.1.1
  invFun S := ⟨⟨S,fun x => !(y x.1)⟩,rfl⟩
  left_inv z := by
    rcases z with ⟨⟨S,b⟩,hb⟩
    apply Subtype.ext
    exact congrArg (Sigma.mk S) hb.symm
  right_inv S := rfl

theorem falsifying_clauses {n w : ℕ} (y : Fin n → Bool) :
    Fintype.card {C : WClause n w // Falsifies y C.1}=n.choose w := by
  classical
  let e : {z : SignedSet n w // z.2=(fun x => !(y x.1))} ≃ {C : WClause n w // Falsifies y C.1} :=
    (equivalence n w).subtypeEquiv (fun z => (falsifies_encode y z.1.1 z.2).symm)
  rw [←Fintype.card_congr e,Fintype.card_congr (fixedSignsEquiv y),varSet_card]

theorem falsification_probability {n w : ℕ} (hw : w ≤ n) (y : Fin n → Bool) :
    uprob (fun C : WClause n w => Falsifies y C.1)=(2 : ℝ)^(-(w : ℤ)) := by
  classical
  unfold uprob
  rw [Finset.filter_congr_decidable Finset.univ (fun C : WClause n w => Falsifies y C.1) (Classical.decPred _),
    ←Fintype.card_subtype,falsifying_clauses,P2MWidthClauseEncoding.card]
  have hc : (n.choose w : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hw).ne'
  push_cast
  rw [zpow_neg,zpow_natCast]
  field_simp

end SemAC02.Supplement.P2MWidthClauseCounts
end

section
-- Inlined Solutions.P2MRandomCNFUnsatisfiability

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MRandomCNFUnsatisfiability

open LiftSAParity P2MProofComplexity.P2MUniformFiniteProbability

attribute [local instance] Classical.propDecidable

theorem sample_nonempty {n w : ℕ} (hw : w ≤ n) : Nonempty (WClause n w) := by
  apply Fintype.card_pos_iff.mp
  rw [P2MWidthClauseEncoding.card]
  exact Nat.mul_pos (Nat.choose_pos hw) (pow_pos (by decide) _)

theorem fixed_assignment {n w m : ℕ} (hw : w ≤ n) (y : Fin n → Bool) :
    uprob (fun ω : Fin m → WClause n w => ∀ j, ¬ Falsifies y (ω j).1)=
      (1-(2 : ℝ)^(-(w : ℤ)))^m := by
  letI := sample_nonempty hw
  rw [independent (fun _ : Fin m => fun C : WClause n w => ¬ Falsifies y C.1)]
  simp only [complement,P2MWidthClauseCounts.falsification_probability hw y,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

theorem satisfiable_probability {n w m : ℕ} (hw : w ≤ n) :
    uprob (fun ω : Fin m → WClause n w => Satisfiable (seqCNF ω)) ≤
      (2 : ℝ)^n*(1-(2 : ℝ)^(-(w : ℤ)))^m := by
  have hb := union_bound (Finset.univ : Finset (Fin n → Bool))
    (fun ω : Fin m → WClause n w => Satisfiable (seqCNF ω))
    (fun y ω => ∀ j, ¬ Falsifies y (ω j).1) (by
      rintro ω ⟨y,hy⟩
      refine ⟨y,Finset.mem_univ _,?_⟩
      intro j
      exact hy (ω j).1 (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  simpa only [fixed_assignment hw,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] using hb

theorem exponential_bound {n w m : ℕ} (hw : w ≤ n) :
    uprob (fun ω : Fin m → WClause n w => Satisfiable (seqCNF ω)) ≤
      Real.exp ((n : ℝ)*Real.log 2-(m : ℝ)*(2 : ℝ)^(-(w : ℤ))) := by
  apply (satisfiable_probability (m:=m) hw).trans
  have hp : 0 ≤ 1-(2 : ℝ)^(-(w : ℤ)) := by
    rw [zpow_neg,zpow_natCast]
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have he : 1-(2 : ℝ)^(-(w : ℤ)) ≤ Real.exp (-(2 : ℝ)^(-(w : ℤ))) := by
    linarith [Real.add_one_le_exp (-(2 : ℝ)^(-(w : ℤ)))]
  calc
    (2 : ℝ)^n*(1-(2 : ℝ)^(-(w : ℤ)))^m ≤
        (2 : ℝ)^n*(Real.exp (-(2 : ℝ)^(-(w : ℤ))))^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp he m) (by positivity)
    _ = _ := by
      have h2 : (2 : ℝ)^n=Real.exp ((n : ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)]
      rw [h2,←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      ring

end SemAC02.Supplement.P2MRandomCNFUnsatisfiability
end

section
-- Inlined Solutions.P2MRandomCNFNeighborhood

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MRandomCNFNeighborhood

open LiftSAParity P2MProofComplexity.P2MUniformFiniteProbability

attribute [local instance] Classical.propDecidable

noncomputable def neighborhood {n w m : ℕ} (ω : Fin m → WClause n w) (J : Finset (Fin m)) : Finset (Fin n) :=
  J.biUnion (fun j => (ω j).1.image Prod.fst)

theorem contained_iff {n w m : ℕ} (ω : Fin m → WClause n w) (J : Finset (Fin m)) (A : Finset (Fin n)) :
    neighborhood ω J⊆A ↔ ∀ j∈J, (ω j).1.image Prod.fst⊆A :=
  Finset.biUnion_subset

theorem containment_bound {n w m : ℕ} (hn : 1 ≤ n) (hw : w ≤ n)
    (J : Finset (Fin m)) (A : Finset (Fin n)) :
    uprob (fun ω : Fin m → WClause n w => neighborhood ω J⊆A) ≤
      ((A.card : ℝ)/(n : ℝ))^(w*J.card) := by
  letI := P2MRandomCNFUnsatisfiability.sample_nonempty hw
  rw [congr _ _ (fun ω => contained_iff ω J A),coordinates J (fun C : WClause n w => C.1.image Prod.fst⊆A)]
  rw [pow_mul]
  exact pow_le_pow_left₀ (nonneg _) (P2MWidthClauseCounts.contained_probability_bound hn hw A) _

theorem small_neighborhood_probability {n w m : ℕ} (hn : 1 ≤ n) (hw : w ≤ n)
    (t u : ℕ) (hu : u ≤ n) :
    uprob (fun ω : Fin m → WClause n w => ∃ J : Finset (Fin m), J.card=t ∧ (neighborhood ω J).card ≤ u) ≤
      (m.choose t : ℝ)*(n.choose u : ℝ)*((u : ℝ)/(n : ℝ))^(w*t) := by
  let JS := (Finset.univ : Finset (Fin m)).powersetCard t
  let AS := (Finset.univ : Finset (Fin n)).powersetCard u
  have hcover : ∀ ω : Fin m → WClause n w,
      (∃ J : Finset (Fin m), J.card=t ∧ (neighborhood ω J).card ≤ u) →
      ∃ z∈JS×ˢAS, neighborhood ω z.1⊆z.2 := by
    rintro ω ⟨J,hJ,hN⟩
    obtain ⟨A,hNA,hAU,hA⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ (neighborhood ω J)) hN
      (by simpa using hu : u ≤ (Finset.univ : Finset (Fin n)).card)
    exact ⟨(J,A),Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hJ⟩,
      Finset.mem_powersetCard.mpr ⟨hAU,hA⟩⟩,hNA⟩
  apply (union_bound (JS×ˢAS) _ (fun z ω => neighborhood ω z.1⊆z.2) hcover).trans
  calc
    (∑ z∈JS×ˢAS, uprob (fun ω : Fin m → WClause n w => neighborhood ω z.1⊆z.2)) ≤
        ∑ _z∈JS×ˢAS, ((u : ℝ)/(n : ℝ))^(w*t) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hzJ,hzA⟩ := Finset.mem_product.mp hz
      have hJ := (Finset.mem_powersetCard.mp hzJ).2
      have hA := (Finset.mem_powersetCard.mp hzA).2
      simpa only [hJ,hA] using containment_bound hn hw z.1 z.2
    _ = _ := by simp [JS,AS,Finset.card_product,Finset.card_powersetCard,Nat.cast_mul]

end SemAC02.Supplement.P2MRandomCNFNeighborhood
end

section
-- Inlined Solutions.P2MRandomThreeCNFExpansionProbability

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MRandomThreeCNFExpansionProbability

open P2MProofComplexity.P2MUniformFiniteProbability P2MRandomCNFNeighborhood P2MRandomThreeCNFEntropy

 theorem single_size (α : ℝ) (hα : 0 < α) (n m t : ℕ) (hn : 3 ≤ n) (hm : 1 ≤ m)
    (ht : 1 ≤ t) (hmα : (m : ℝ) ≤ α*n) (htn : (t : ℝ)/n ≤ expansionFraction α) :
    uprob (fun ω : Fin m → WClause n 3 => ∃ J : Finset (Fin m), J.card=t ∧
      ((neighborhood ω J).card : ℝ)<15*(t : ℝ)/8) ≤
        Real.exp (-Real.log n/16-((t : ℝ)-1)) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  let u := ⌊15*(t : ℝ)/8⌋₊
  have hu : 1 ≤ u := Nat.le_floor (by norm_num; linarith)
  have huU : (u : ℝ) ≤ 15*(t : ℝ)/8 := Nat.floor_le (by positivity)
  have htSmall : (t : ℝ)/n ≤ 1/2 := htn.trans (fraction_bounds α).2
  have hun : u ≤ n := by
    have htHalf := (div_le_iff₀ hnR).mp htSmall
    have hh : (u : ℝ) ≤ n := by linarith
    exact_mod_cast hh
  apply (mono _ (fun ω : Fin m → WClause n 3 => ∃ J : Finset (Fin m),
    J.card=t ∧ (neighborhood ω J).card ≤ u) (by
      rintro ω ⟨J,hJ,hbad⟩
      exact ⟨J,hJ,Nat.le_floor hbad.le⟩)).trans
  apply (small_neighborhood_probability (by omega) hn t u hun).trans
  exact union_term α hα n m t u (by omega) hm ht hu huU hmα htn

 theorem geometric_zero (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (s : ℕ) :
    (∑ j∈Finset.range s, q^j) ≤ 1/(1-q) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-q)).mpr
  have he := geom_sum_mul q s
  have hp := pow_nonneg hq0 s
  nlinarith

 theorem failure_probability (α : ℝ) (hα : 0 < α) (n m s : ℕ) (hn : 3 ≤ n) (hm : 1 ≤ m)
    (hmα : (m : ℝ) ≤ α*n) (hs : (s : ℝ)/n ≤ expansionFraction α) :
    uprob (fun ω : Fin m → WClause n 3 => ∃ J : Finset (Fin m), J.Nonempty ∧ J.card ≤ s ∧
      ((neighborhood ω J).card : ℝ)<15*(J.card : ℝ)/8) ≤
        Real.exp (-Real.log n/16)/(1-Real.exp (-1)) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hcover : ∀ ω : Fin m → WClause n 3,
      (∃ J : Finset (Fin m), J.Nonempty ∧ J.card ≤ s ∧ ((neighborhood ω J).card : ℝ)<15*(J.card : ℝ)/8) →
      ∃ j∈Finset.range s, ∃ J : Finset (Fin m), J.card=j+1 ∧
        ((neighborhood ω J).card : ℝ)<15*((j+1 : ℕ) : ℝ)/8 := by
    rintro ω ⟨J,hJ,hJs,hbad⟩
    have hpos := Finset.card_pos.mpr hJ
    exact ⟨J.card-1,Finset.mem_range.mpr (by omega),J,by omega,by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ J.card)] using hbad⟩
  apply (union_bound (Finset.range s) _
    (fun j ω => ∃ J : Finset (Fin m), J.card=j+1 ∧ ((neighborhood ω J).card : ℝ)<15*((j+1 : ℕ) : ℝ)/8) hcover).trans
  calc
    _ ≤ ∑ j∈Finset.range s, Real.exp (-Real.log n/16)*Real.exp (-1)^j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjs : j+1 ≤ s := by have hh := Finset.mem_range.mp hj; omega
      have ht : ((j+1 : ℕ) : ℝ)/n ≤ expansionFraction α := by
        apply le_trans _ hs
        exact div_le_div_of_nonneg_right (by exact_mod_cast hjs) hnR.le
      have hb := single_size α hα n m (j+1) hn hm (by omega) hmα ht
      have he : Real.exp (-Real.log n/16-(((j+1 : ℕ) : ℝ)-1))=
          Real.exp (-Real.log n/16)*Real.exp (-1)^j := by
        rw [←Real.exp_nat_mul,←Real.exp_add]
        congr 1
        push_cast
        ring
      rwa [he] at hb
    _ = Real.exp (-Real.log n/16)*(∑ j∈Finset.range s, Real.exp (-1)^j) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-Real.log n/16)*(1/(1-Real.exp (-1))) :=
      mul_le_mul_of_nonneg_left (geometric_zero _ (Real.exp_pos _).le (by simpa using (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ)<0))) s) (Real.exp_pos _).le
    _ = _ := by ring

end SemAC02.Supplement.P2MRandomThreeCNFExpansionProbability
end

section
-- Inlined Solutions.P2MCNFBoundaryExpansion

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MCNFBoundaryExpansion

open LiftSAParity P2MProofComplexity.P2MFiniteFamilyBoundary P2MExpansionCNFRepresentation

variable {n w m : ℕ}

theorem boundary_eq (ω : Fin m → WClause n w) (J : Finset (Fin m)) :
    PCNonBool.boundaryOn (representation (fun j => (ω j).1)).graph Finset.univ J=
      boundary (fun j => (ω j).1.image Prod.fst) J := by
  classical
  let C := fun j => (ω j).1.image Prod.fst
  have hfilter (v : Fin n) :
      J.filter (fun j => (representation (fun i => (ω i).1)).graph.Adj j v)=J.filter (fun j => v∈C j) := by
    ext j
    simp only [Finset.mem_filter,graph_iff _ (fun i => P2MCNFExpansionPolynomials.wclause_consistent (ω i)),C]
  ext v
  simp only [PCNonBool.boundaryOn,Finset.mem_filter,Finset.mem_univ,true_and,hfilter,boundary,P2MProofComplexity.P2MFiniteFamilyBoundary.multiplicity]
  constructor
  · intro hv
    refine ⟨?_,hv⟩
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (by omega : 0 < (J.filter (fun j => v∈C j)).card)
    exact Finset.mem_biUnion.mpr ⟨j,(Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2⟩
  · exact And.right

theorem from_neighborhood (ω : Fin m → WClause n w) (s : ℕ)
    (hN : ∀ J : Finset (Fin m), J.Nonempty → J.card ≤ s →
      (3 : ℝ)*w*J.card/4 ≤ (P2MRandomCNFNeighborhood.neighborhood ω J).card) :
    IsBdryExp (representation (fun j => (ω j).1)).graph s ((w : ℝ)/2) := by
  intro J hJs
  have hJsn : J.card ≤ s := by exact_mod_cast hJs
  by_cases hne : J.Nonempty
  · have hb := boundary_bound (fun j => (ω j).1.image Prod.fst) J
    have hsum : (∑ j∈J, ((ω j).1.image Prod.fst).card)=w*J.card := by
      simp only [(fun j => (ω j).2.2),Finset.sum_const,smul_eq_mul,Nat.mul_comm]
    rw [hsum] at hb
    have hbR : 2*((P2MRandomCNFNeighborhood.neighborhood ω J).card : ℝ) ≤
        ((boundary (fun j => (ω j).1.image Prod.fst) J).card : ℝ)+(w : ℝ)*J.card := by exact_mod_cast hb
    rw [boundary_eq]
    have hn := hN J hne hJsn
    nlinarith
  · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst J
    simp [PCNonBool.boundaryOn]

end SemAC02.Supplement.P2MCNFBoundaryExpansion
end

section
-- Inlined Solutions.P2MRandomThreeCNFExpansion

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MRandomThreeCNFExpansion

open Filter Topology LiftSAParity P2MProofComplexity.P2MUniformFiniteProbability
open P2MRandomThreeCNFEntropy

attribute [local instance] Classical.propDecidable

noncomputable def supportSize (α : ℝ) (n : ℕ) : ℕ := ⌊expansionFraction α*n⌋₊

def Bad (α : ℝ) (n : ℕ) (ω : Fin ⌊α*n⌋₊ → WClause n 3) : Prop :=
  ∃ J : Finset (Fin ⌊α*n⌋₊), J.Nonempty ∧ J.card ≤ supportSize α n ∧
    ((P2MRandomCNFNeighborhood.neighborhood ω J).card : ℝ)<15*(J.card : ℝ)/8

 theorem failure_tends_zero (α : ℝ) (hα : 0 < α) :
    Tendsto (fun n : ℕ => uprob (Bad α n)) atTop (𝓝 0) := by
  have hFraction : 0 < expansionFraction α := (fraction_bounds α).1
  have hLog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hScale := Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ)<16) hLog
  have hExp : Tendsto (fun n : ℕ => Real.exp (-Real.log n/16)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hScale
  have hTail : Tendsto (fun n : ℕ => Real.exp (-Real.log n/16)/(1-Real.exp (-1))) atTop (𝓝 0) := by
    simpa only [zero_div] using hExp.div_const (1-Real.exp (-1))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => nonneg _)) _ hTail
  have hLarge := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop (2/α)
  filter_upwards [eventually_ge_atTop 3,hLarge] with n hn hLarge
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hmα : (⌊α*n⌋₊ : ℝ) ≤ α*n := Nat.floor_le (by positivity)
  have hm : 1 ≤ ⌊α*(n : ℝ)⌋₊ := by
    apply Nat.le_floor
    norm_num
    have hh := (div_le_iff₀ hα).mp hLarge
    nlinarith
  have hs : (supportSize α n : ℝ)/n ≤ expansionFraction α := by
    have hf : (supportSize α n : ℝ) ≤ expansionFraction α*n := Nat.floor_le (by positivity)
    exact (div_le_iff₀ hnR).mpr hf
  exact P2MRandomThreeCNFExpansionProbability.failure_probability α hα n ⌊α*n⌋₊ (supportSize α n) hn hm hmα hs

 theorem no_bad_tends_one (α : ℝ) (hα : 0 < α) :
    Tendsto (fun n : ℕ => uprob (fun ω => ¬ Bad α n ω)) atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (failure_tends_zero α hα)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  letI := P2MRandomCNFUnsatisfiability.sample_nonempty hn
  exact (complement (Bad α n)).symm

 theorem neighborhood_eq {n m : ℕ} (ω : Fin m → WClause n 3) (J : Finset (Fin m)) :
    P2MProofComplexity.P2MBipartiteNeighborhoodExpansion.neighbors
      (P2MExpansionCNFRepresentation.representation (fun j => (ω j).1)).graph J=
      P2MRandomCNFNeighborhood.neighborhood ω J := by
  ext v
  simp only [P2MProofComplexity.P2MBipartiteNeighborhoodExpansion.mem_neighbors,
    P2MExpansionCNFRepresentation.graph_iff _ (fun j => P2MCNFExpansionPolynomials.wclause_consistent (ω j)),
    P2MRandomCNFNeighborhood.neighborhood,Finset.mem_biUnion]

 theorem clause_neighbors {n m : ℕ} (ω : Fin m → WClause n 3) (j : Fin m) :
    PCNonBool.nbrOn (P2MExpansionCNFRepresentation.representation (fun j => (ω j).1)).graph Finset.univ j=
      (ω j).1.image Prod.fst := by
  ext v
  simp only [PCNonBool.nbrOn,Finset.mem_filter,Finset.mem_univ,true_and,
    P2MExpansionCNFRepresentation.graph_iff _ (fun j => P2MCNFExpansionPolynomials.wclause_consistent (ω j))]

 theorem left_degree {n m : ℕ} (ω : Fin m → WClause n 3) (j : Fin m) :
    (PCNonBool.nbrOn (P2MExpansionCNFRepresentation.representation (fun j => (ω j).1)).graph Finset.univ j).card=3 := by
  rw [clause_neighbors]
  exact (ω j).2.2

 theorem expansion_of_no_bad (α : ℝ) (n : ℕ) (ω : Fin ⌊α*n⌋₊ → WClause n 3) (hω : ¬ Bad α n ω) :
    P2MProofComplexity.P2MBipartiteNeighborhoodExpansion.Expands
      (P2MExpansionCNFRepresentation.representation (fun j => (ω j).1)).graph (expansionFraction α*n) (15/8) ∧
    IsBdryExp (P2MExpansionCNFRepresentation.representation (fun j => (ω j).1)).graph (expansionFraction α*n) (3/4) := by
  have hN : ∀ J : Finset (Fin ⌊α*n⌋₊), (J.card : ℝ) ≤ expansionFraction α*n →
      (15/8 : ℝ)*J.card ≤ (P2MRandomCNFNeighborhood.neighborhood ω J).card := by
    intro J hJs
    by_cases hJ : J.Nonempty
    · by_contra hh
      exact hω ⟨J,hJ,Nat.le_floor hJs,by nlinarith [lt_of_not_ge hh]⟩
    · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      subst J
      simp [P2MRandomCNFNeighborhood.neighborhood]
  refine ⟨?_,?_⟩
  · intro J hJs
    rw [neighborhood_eq]
    exact hN J hJs
  · intro J hJs
    have hb := P2MProofComplexity.P2MFiniteFamilyBoundary.boundary_bound (fun j => (ω j).1.image Prod.fst) J
    have hsum : (∑ j∈J, ((ω j).1.image Prod.fst).card)=3*J.card := by
      simp only [(fun j => (ω j).2.2),Finset.sum_const,smul_eq_mul,Nat.mul_comm]
    rw [hsum] at hb
    have hbR : 2*((P2MRandomCNFNeighborhood.neighborhood ω J).card : ℝ) ≤
      ((P2MProofComplexity.P2MFiniteFamilyBoundary.boundary (fun j => (ω j).1.image Prod.fst) J).card : ℝ)+3*J.card := by exact_mod_cast hb
    rw [P2MCNFBoundaryExpansion.boundary_eq]
    have hn := hN J hJs
    nlinarith

 theorem full (α : ℝ) (hα : 0 < α) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ Tendsto (fun n : ℕ => uprob (fun ω : Fin ⌊α*n⌋₊ → WClause n 3 =>
      P2MProofComplexity.P2MBipartiteNeighborhoodExpansion.Expands
        (P2MExpansionCNFRepresentation.representation (fun j => (ω j).1)).graph (γ*n) (15/8) ∧
      IsBdryExp (P2MExpansionCNFRepresentation.representation (fun j => (ω j).1)).graph (γ*n) (3/4))) atTop (𝓝 1) := by
  refine ⟨expansionFraction α,(fraction_bounds α).1,(fraction_bounds α).2.trans (by norm_num),?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (no_bad_tends_one α hα) tendsto_const_nhds _ (fun n => le_one _)
  intro n
  exact mono _ _ (fun ω hω => expansion_of_no_bad α n ω hω)

end SemAC02.Supplement.P2MRandomThreeCNFExpansion
end

section
-- Inlined Solutions.P2MRandomThreeCNFUnsatisfiability

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MRandomThreeCNFUnsatisfiability

open Filter Topology LiftSAParity P2MProofComplexity.P2MUniformFiniteProbability

theorem probability_bound (α : ℝ) (n : ℕ) (hn : 3 ≤ n) :
    uprob (fun ω : Fin ⌊α*n⌋₊ → WClause n 3 => Satisfiable (seqCNF ω)) ≤
      Real.exp ((n : ℝ)*(Real.log 2-α*Real.log (8/7))+Real.log (8/7)) := by
  apply (P2MRandomCNFUnsatisfiability.satisfiable_probability (m:=⌊α*n⌋₊) hn).trans
  have hbase : 1-(2 : ℝ)^(-((3 : ℕ) : ℤ))=7/8 := by norm_num
  rw [hbase]
  have hlog : Real.log (7/8) = -Real.log (8/7) := by
    have he : (7/8 : ℝ)=(8/7)⁻¹ := by norm_num
    rw [he,Real.log_inv]
  have h2 : (2 : ℝ)^n=Real.exp ((n : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)]
  have hq : (7/8 : ℝ)^⌊α*n⌋₊=Real.exp ((⌊α*n⌋₊ : ℝ)*Real.log (7/8)) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<7/8)]
  rw [h2,hq,←Real.exp_add,hlog]
  apply Real.exp_le_exp.mpr
  have hl : 0 < Real.log (8/7) := Real.log_pos (by norm_num)
  have hf := Nat.sub_one_lt_floor (α*(n : ℝ))
  nlinarith

theorem satisfiable_tends_zero (α : ℝ) (hα : Real.log 2/Real.log (8/7)<α) :
    Tendsto (fun n : ℕ => uprob (fun ω : Fin ⌊α*n⌋₊ → WClause n 3 => Satisfiable (seqCNF ω))) atTop (𝓝 0) := by
  have hl : 0 < Real.log (8/7) := Real.log_pos (by norm_num)
  have hc : Real.log 2-α*Real.log (8/7)<0 := by have hh := (div_lt_iff₀ hl).mp hα; linarith
  have ht : Tendsto (fun n : ℕ => Real.exp ((n : ℝ)*(Real.log 2-α*Real.log (8/7))+Real.log (8/7))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact Filter.tendsto_atBot_add_const_right atTop (Real.log (8/7))
      (Filter.Tendsto.atTop_mul_const_of_neg hc tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact probability_bound α n hn

theorem unsatisfiable_tends_one (α : ℝ) (hα : Real.log 2/Real.log (8/7)<α) :
    Tendsto (fun n : ℕ => uprob (fun ω : Fin ⌊α*n⌋₊ → WClause n 3 => ¬ Satisfiable (seqCNF ω))) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (satisfiable_tends_zero α hα)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  letI := P2MRandomCNFUnsatisfiability.sample_nonempty hn
  simpa only [sub_zero] using (complement (fun ω : Fin ⌊α*n⌋₊ → WClause n 3 => Satisfiable (seqCNF ω))).symm

end SemAC02.Supplement.P2MRandomThreeCNFUnsatisfiability
end

section
-- Inlined Solutions.P2MRandomThreeCNFLowerBound

set_option maxHeartbeats 4000000

namespace SemAC02.Supplement.P2MRandomThreeCNFLowerBound

open ACirc Filter Topology LiftSAParity P2MProofComplexity.P2MUniformFiniteProbability

theorem full (α : ℝ) (hα : 0 < α) :
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => uprob (fun ω : Fin ⌊α*n⌋₊ → WClause n 3 =>
      ∀ π : List (ACirc (ZMod 2) (Fin n)),
        IsSemPCRef IsSPS Set.univ (clauseAx (seqCNF ω : Set (Clause (Fin n)))) π →
        (2 : ℝ)^(c*n) ≤ topS Set.univ π ∧ (2 : ℝ)^(c*n) ≤ csize π)) atTop (𝓝 1)) ∧
    (Real.log 2/Real.log (8/7) < α →
      Tendsto (fun n : ℕ => uprob (fun ω : Fin ⌊α*n⌋₊ → WClause n 3 =>
        ¬ Satisfiable (seqCNF ω))) atTop (𝓝 1)) := by
  refine ⟨?_, P2MRandomThreeCNFUnsatisfiability.unsatisfiable_tends_one α⟩
  let γ := P2MRandomThreeCNFEntropy.expansionFraction α
  let d := P2MProofComplexity.P2MRightDegreeReduction.degreeBound α γ
  let η := P2MRandomCNFLinearParameters.fraction γ d
  have hγ : 0 < γ := (P2MRandomThreeCNFEntropy.fraction_bounds α).1
  have hγ1 : γ ≤ 1 := (P2MRandomThreeCNFEntropy.fraction_bounds α).2.trans (by norm_num)
  have hη : 0 < η := P2MRandomCNFLinearParameters.fraction_pos γ d hγ
  refine ⟨η^2/32, by positivity, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (P2MRandomThreeCNFExpansion.no_bad_tends_one α hα)
    tendsto_const_nhds _ (Filter.Eventually.of_forall (fun n => le_one _))
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLarge := (Filter.Tendsto.const_mul_atTop hγ hNat).eventually_ge_atTop 64
  have hDegree := (Filter.Tendsto.const_mul_atTop hη hNat).eventually_ge_atTop 4
  have hExponent := (Filter.Tendsto.const_mul_atTop (sq_pos_of_pos hη) hNat).eventually_ge_atTop 32
  filter_upwards [hLarge, hDegree, hExponent] with n hn hk hExp
  apply mono
  intro ω hω π hπ
  have hRange : (seqCNF ω : Set (Clause (Fin n))) = Set.range (fun j => (ω j).1) := by
    ext C
    simp [seqCNF]
  rw [hRange] at hπ
  exact P2MRandomThreeCNFDeterministicBound.lower (fun j => (ω j).1)
    (fun j => P2MCNFExpansionPolynomials.wclause_consistent (ω j)) (fun j => (ω j).2.1)
    α γ hγ hγ1 (by simpa only [Fintype.card_fin] using Nat.floor_le (by positivity : 0 ≤ α*(n : ℝ)))
    hn hk hExp (P2MRandomThreeCNFExpansion.expansion_of_no_bad α n ω hω).1 π hπ

end SemAC02.Supplement.P2MRandomThreeCNFLowerBound
end

end P2MRandomThreeCNFProof
open SemAC02.Supplement MvPolynomial ACirc Filter Topology

theorem solution (α : ℝ) (hα : 0 < α) :
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => uprob (fun ω : Fin ⌊α * n⌋₊ → WClause n 3 =>
      ∀ π : List (ACirc (ZMod 2) (Fin n)),
        IsSemPCRef IsSPS Set.univ (clauseAx (seqCNF ω : Set (LiftSAParity.Clause (Fin n)))) π →
        (2 : ℝ) ^ (c * n) ≤ topS Set.univ π ∧ (2 : ℝ) ^ (c * n) ≤ csize π)) atTop (𝓝 1)) ∧
    (Real.log 2 / Real.log (8 / 7) < α →
      Tendsto (fun n : ℕ => uprob (fun ω : Fin ⌊α * n⌋₊ → WClause n 3 =>
        ¬ LiftSAParity.Satisfiable (seqCNF ω))) atTop (𝓝 1))  := by
  exact P2MRandomThreeCNFProof.SemAC02.Supplement.P2MRandomThreeCNFLowerBound.full α hα
