-- Prove2me | solution 1 for SemAC02.Supplement.theorem_6_12_functional_graph_php
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T12:59:16.356819+00:00
-- url     : https://prove2.me/submissions/68e30a03-f05f-476f-918a-f99b9da9d47d

import Definitions.Def_SemAC02_Supplement_fphpG
import Mathlib
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_SemAC02_Supplement_expansionRank
import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Ble
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Supplement_randCNF
import Definitions.Def_AC02Frege_PC
import Definitions.Def_SemAC02_Supplement_ResXor
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_SemAC02_Supplement_IsPseudoRed
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Definitions.Def_PCNonBool_IsDerivation
import Theorems.Thm_SemAC02_Supplement_theorem_4_4_sps_size_bound

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MFunctionalPHPProof
section
-- Inlined Solutions.P2MFunctionalPHPMatchingVariables

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MFunctionalPHPMatchingVariables

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def matchingEdge (G : PCNonBool.BipGraph L R) (μ : R → L) (v : R) : Edge (addMatching G μ) :=
  ⟨(μ v, v), Or.inr rfl⟩

theorem matchingEdge_injective (G : PCNonBool.BipGraph L R) (μ : R → L) :
    Function.Injective (matchingEdge G μ) := by
  intro v w he
  exact congrArg (fun e : Edge (addMatching G μ) => e.val.2) he

abbrev Free (G : PCNonBool.BipGraph L R) (μ : R → L) :=
  {e : Edge (addMatching G μ) // e.val.1 ≠ μ e.val.2}

def matchedEquiv (G : PCNonBool.BipGraph L R) (μ : R → L) :
    {e : Edge (addMatching G μ) // e.val.1 = μ e.val.2} ≃ R where
  toFun e := e.val.val.2
  invFun v := ⟨matchingEdge G μ v, rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.property.symm rfl
  right_inv _ := rfl

theorem free_card (G : PCNonBool.BipGraph L R) (μ : R → L) :
    Fintype.card (Free G μ) + Fintype.card R = Fintype.card (Edge (addMatching G μ)) := by
  have hm : Fintype.card {e : Edge (addMatching G μ) // e.val.1 = μ e.val.2} = Fintype.card R :=
    Fintype.card_congr (matchedEquiv G μ)
  have hf := Fintype.card_subtype_compl (fun e : Edge (addMatching G μ) => e.val.1 = μ e.val.2)
  rw [hm] at hf
  have hle := Fintype.card_le_of_injective (matchingEdge G μ) (matchingEdge_injective G μ)
  change Fintype.card (Free G μ) = Fintype.card (Edge (addMatching G μ))-Fintype.card R at hf
  omega

theorem unmatched {n : ℕ} (μ : Fin n → Fin (n+1)) (hμ : Function.Injective μ) :
    ∃ u : Fin (n+1), ∀ w, w ≠ u ↔ ∃ v, μ v = w := by
  classical
  let M := Finset.univ.image μ
  have hM : M.card = n := by rw [Finset.card_image_of_injective _ hμ]; simp
  have hC : ((Finset.univ : Finset (Fin (n+1))) \ M).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hM]
    omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hC
  refine ⟨u, ?_⟩
  intro w
  have he : w ∉ M ↔ w = u := by
    have hh : w ∈ ((Finset.univ : Finset (Fin (n+1))) \ M) ↔ w ∈ ({u} : Finset (Fin (n+1))) := by rw [hu]
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] using hh
  have hmem : w ∈ M ↔ ∃ v, μ v = w := by simp [M]
  rw [← hmem]
  tauto

abbrev Selected (G : PCNonBool.BipGraph L R) (μ : R → L) :=
  {e : Edge (addMatching G μ) // e.val.1 ≠ μ e.val.2 ∧ ∃ v, μ v = e.val.1}

noncomputable def reserved (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Selected G μ) : R :=
  Classical.choose e.property.2

theorem reserved_spec (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Selected G μ) :
    μ (reserved G μ e) = e.val.val.1 := Classical.choose_spec e.property.2

end SemAC02.Supplement.P2MFunctionalPHPMatchingVariables
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

theorem product_count (B : V → Finset V) (b : ℕ) (hB : ∀ v, (B v).card ≤ b)
    (hself : ∀ v, v ∈ B v) (hsymm : ∀ v w, w ∈ B v → v ∈ B w) (k : ℕ) :
    (∏ i ∈ Finset.range k, (Fintype.card V-b*i)) ≤ k.factorial * (sets B k).card := by
  classical
  induction k with
  | zero =>
    have hempty : (∅ : Finset V) ∈ sets B 0 := by rw [mem_sets]; simp [Good]
    simpa using Finset.card_pos.mpr ⟨∅, hempty⟩
  | succ k ih =>
    rw [Finset.prod_range_succ]
    calc
      _ ≤ (k.factorial*(sets B k).card)*(Fintype.card V-b*k) := Nat.mul_le_mul_right _ ih
      _ = k.factorial*((Fintype.card V-b*k)*(sets B k).card) := by ring
      _ ≤ k.factorial*((k+1)*(sets B (k+1)).card) :=
        Nat.mul_le_mul_left _ (step B b hB hself hsymm k)
      _ = (k+1).factorial*(sets B (k+1)).card := by rw [Nat.factorial_succ]; ring

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
-- Inlined Solutions.P2MCompatibleFamilyCounting

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MCompatibleFamilyCounting

variable {E W : Type} [Fintype E] [DecidableEq E] [DecidableEq W]

noncomputable def conflicts (N : E → Finset W) (e : E) : Finset E :=
  (N e).biUnion (fun w => Finset.univ.filter (fun e' => w ∈ N e'))

theorem mem_conflicts (N : E → Finset W) (e e' : E) :
    e' ∈ conflicts N e ↔ ¬ Disjoint (N e) (N e') := by
  simp only [conflicts, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.not_disjoint_iff]

theorem conflict_card (N : E → Finset W) (a b : ℕ)
    (hN : ∀ e, (N e).card ≤ a)
    (hW : ∀ w, (Finset.univ.filter (fun e => w ∈ N e)).card ≤ b) (e : E) :
    (conflicts N e).card ≤ a*b := by
  calc
    _ ≤ ∑ w ∈ N e, (Finset.univ.filter (fun e' => w ∈ N e')).card := Finset.card_biUnion_le
    _ ≤ ∑ w ∈ N e, b := Finset.sum_le_sum (fun w _ => hW w)
    _ = (N e).card*b := by simp
    _ ≤ a*b := Nat.mul_le_mul_right _ (hN e)

theorem count (N : E → Finset W) (a b : ℕ)
    (hne : ∀ e, (N e).Nonempty) (hN : ∀ e, (N e).card ≤ a)
    (hW : ∀ w, (Finset.univ.filter (fun e => w ∈ N e)).card ≤ b) (k : ℕ) :
    (∏ i ∈ Finset.range k, (Fintype.card E-a*b*i)) ≤
      k.factorial*(P2MSeparatedSetCounting.sets (conflicts N) k).card ∧
    (Fintype.card E-a*b*(k-1))^k ≤
      k.factorial*(P2MSeparatedSetCounting.sets (conflicts N) k).card := by
  have hself (e : E) : e ∈ conflicts N e := by
    apply (mem_conflicts N e e).mpr
    obtain ⟨w, hw⟩ := hne e
    exact Finset.not_disjoint_iff.mpr ⟨w, hw, hw⟩
  have hsymm (e e' : E) (h : e' ∈ conflicts N e) : e ∈ conflicts N e' := by
    rw [mem_conflicts] at h ⊢
    exact fun hd => h hd.symm
  exact ⟨P2MSeparatedSetCounting.product_count _ _ (conflict_card N a b hN hW) hself hsymm k,
    P2MSeparatedSetCounting.count _ _ (conflict_card N a b hN hW) hself hsymm k⟩

end P2MProofComplexity.P2MCompatibleFamilyCounting
end

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
-- Inlined Solutions.P2MCompatibleEdgeNeighborhoods

set_option maxHeartbeats 3000000

namespace P2MProofComplexity.P2MCompatibleEdgeNeighborhoods

open PCNonBool P2MCleaningDegreeReduction

variable {L R E : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    [Fintype E] [DecidableEq E]

noncomputable def family (G : BipGraph L R) (reserved hole : E → R) (e : E) : Finset L :=
  (Finset.univ.filter (fun u => G.Adj u (reserved e))) ∪
    (Finset.univ.filter (fun u => G.Adj u (hole e)))

theorem hole_fiber (G : BipGraph L R) (row : E → L) (hole : E → R)
    (hinj : ∀ e e', row e = row e' → hole e = hole e' → e = e')
    (hEdge : ∀ e, G.Adj (row e) (hole e)) (dR : ℕ)
    (hR : ∀ v, rightDegree G v ≤ dR) (v : R) :
    (Finset.univ.filter (fun e => hole e = v)).card ≤ dR := by
  let S := Finset.univ.filter (fun e => hole e = v)
  let T := Finset.univ.filter (fun u => G.Adj u v)
  let f : S → T := fun e => ⟨row e.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    have he := (Finset.mem_filter.mp e.property).2
    rw [← he]
    exact hEdge e.val⟩⟩
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    exact hinj e.val e'.val (congrArg Subtype.val he)
      ((Finset.mem_filter.mp e.property).2.trans (Finset.mem_filter.mp e'.property).2.symm)
  have hh : S.card ≤ T.card := by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  exact hh.trans (hR v)

theorem reserved_fiber (G : BipGraph L R) (μ : R → L) (row : E → L) (hole reserved : E → R)
    (hinj : ∀ e e', row e = row e' → hole e = hole e' → e = e')
    (hEdge : ∀ e, G.Adj (row e) (hole e)) (hreserved : ∀ e, μ (reserved e) = row e)
    (dL : ℕ) (hL : ∀ u, (nbrOn G Finset.univ u).card ≤ dL) (v : R) :
    (Finset.univ.filter (fun e => reserved e = v)).card ≤ dL := by
  let S := Finset.univ.filter (fun e => reserved e = v)
  let T := nbrOn G Finset.univ (μ v)
  have hrow (e : S) : row e.val = μ v := by
    rw [← hreserved e.val, (Finset.mem_filter.mp e.property).2]
  let f : S → T := fun e => ⟨hole e.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    rw [← hrow e]
    exact hEdge e.val⟩⟩
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    exact hinj e.val e'.val ((hrow e).trans (hrow e').symm) (congrArg Subtype.val he)
  have hh : S.card ≤ T.card := by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  exact hh.trans (hL (μ v))

theorem incidence_bound (G : BipGraph L R) (μ : R → L) (row : E → L) (hole reserved : E → R)
    (hinj : ∀ e e', row e = row e' → hole e = hole e' → e = e')
    (hEdge : ∀ e, G.Adj (row e) (hole e)) (hreserved : ∀ e, μ (reserved e) = row e)
    (dL dR : ℕ) (hL : ∀ u, (nbrOn G Finset.univ u).card ≤ dL)
    (hR : ∀ v, rightDegree G v ≤ dR) (w : L) :
    (Finset.univ.filter (fun e => w ∈ family G reserved hole e)).card ≤ dL*(dR+dL) := by
  let F (v : R) := (Finset.univ.filter (fun e => hole e = v)) ∪
    (Finset.univ.filter (fun e => reserved e = v))
  have hsub : Finset.univ.filter (fun e => w ∈ family G reserved hole e) ⊆
      (nbrOn G Finset.univ w).biUnion F := by
    intro e he
    have hwe := (Finset.mem_filter.mp he).2
    rcases Finset.mem_union.mp hwe with hp | hv
    · apply Finset.mem_biUnion.mpr
      refine ⟨reserved e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, ?_⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    · apply Finset.mem_biUnion.mpr
      refine ⟨hole e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩, ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  have hF (v : R) : (F v).card ≤ dR+dL :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add
      (hole_fiber G row hole hinj hEdge dR hR v)
      (reserved_fiber G μ row hole reserved hinj hEdge hreserved dL hL v))
  calc
    _ ≤ ((nbrOn G Finset.univ w).biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ nbrOn G Finset.univ w, (F v).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ nbrOn G Finset.univ w, (dR+dL) := Finset.sum_le_sum (fun v _ => hF v)
    _ = (nbrOn G Finset.univ w).card*(dR+dL) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (hL w)

theorem count (G : BipGraph L R) (μ : R → L) (row : E → L) (hole reserved : E → R)
    (hinj : ∀ e e', row e = row e' → hole e = hole e' → e = e')
    (hEdge : ∀ e, G.Adj (row e) (hole e)) (hreserved : ∀ e, μ (reserved e) = row e)
    (hMatched : ∀ e, G.Adj (row e) (reserved e))
    (dL dR : ℕ) (hL : ∀ u, (nbrOn G Finset.univ u).card ≤ dL)
    (hR : ∀ v, rightDegree G v ≤ dR) (k : ℕ) :
    (∏ i ∈ Finset.range k, (Fintype.card E-(2*dR*dL*(dR+dL))*i)) ≤
      k.factorial*(P2MSeparatedSetCounting.sets (P2MCompatibleFamilyCounting.conflicts (family G reserved hole)) k).card ∧
    (Fintype.card E-(2*dR*dL*(dR+dL))*(k-1))^k ≤
      k.factorial*(P2MSeparatedSetCounting.sets (P2MCompatibleFamilyCounting.conflicts (family G reserved hole)) k).card := by
  have hne (e : E) : (family G reserved hole e).Nonempty := by
    refine ⟨row e, Finset.mem_union_left _ ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMatched e⟩
  have hsize (e : E) : (family G reserved hole e).card ≤ 2*dR := by
    exact (Finset.card_union_le _ _).trans (by simpa only [two_mul, rightDegree] using Nat.add_le_add (hR (reserved e)) (hR (hole e)))
  simpa only [Nat.mul_assoc] using P2MCompatibleFamilyCounting.count (family G reserved hole)
    (2*dR) (dL*(dR+dL)) hne hsize
    (incidence_bound G μ row hole reserved hinj hEdge hreserved dL dR hL hR) k

end P2MProofComplexity.P2MCompatibleEdgeNeighborhoods
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
-- Inlined Solutions.P2MBipartiteDeletionExpansion

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MBipartiteDeletionExpansion

open PCNonBool P2MBipartiteInducedSubgraph SemAC02.Supplement

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem boundary_image (G : BipGraph L R) (I : Finset L) (K : Finset R)
    (J : Finset {u // u ∉ I}) :
    (boundaryOn (graph G I K) Finset.univ J).map (Function.Embedding.subtype _) =
      boundaryOn G Finset.univ (J.map (Function.Embedding.subtype _)) \ K := by
  classical
  let J' := J.map (Function.Embedding.subtype (fun u => u ∉ I))
  have hcount (v : R) : (J.filter (fun u => G.Adj u.val v)).card =
      (J'.filter (fun u => G.Adj u v)).card := by
    have he : (J.filter (fun u => G.Adj u.val v)).map (Function.Embedding.subtype _) =
        J'.filter (fun u => G.Adj u v) := by
      dsimp only [J']
      rw [Finset.filter_map]
      rfl
    simpa only [Finset.card_map] using congrArg Finset.card he
  ext v
  constructor
  · intro hv
    obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, v'.property⟩
    exact (hcount v'.val).symm.trans (Finset.mem_filter.mp hv').2
  · intro hv
    obtain ⟨hv, hvK⟩ := Finset.mem_sdiff.mp hv
    refine Finset.mem_map.mpr ⟨⟨v, hvK⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact (hcount v).trans (Finset.mem_filter.mp hv).2

theorem boundary_loss (G : BipGraph L R) (J : Finset L) (K : Finset R) :
    (boundaryOn G Finset.univ J).card ≤
      (boundaryOn G Finset.univ J \ K).card+∑ u ∈ J, (nbrOn G K u).card := by
  classical
  have hsub : boundaryOn G Finset.univ J ⊆
      (boundaryOn G Finset.univ J \ K) ∪ J.biUnion (nbrOn G K) := by
    intro v hv
    by_cases hvK : v ∈ K
    · apply Finset.mem_union_right
      have hcard := (Finset.mem_filter.mp hv).2
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (J.filter (fun u => G.Adj u v)).card)
      have hu' := Finset.mem_filter.mp hu
      exact Finset.mem_biUnion.mpr ⟨u, hu'.1, Finset.mem_filter.mpr ⟨hvK, hu'.2⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hvK⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))

theorem expansion (G : BipGraph L R) (I : Finset L) (K : Finset R)
    (s δ : ℝ) (hG : IsBdryExp G s δ) (t : ℕ)
    (hdeleted : ∀ u, u ∉ I → (nbrOn G K u).card ≤ t) :
    IsBdryExp (graph G I K) s (δ-t) := by
  classical
  intro J hJs
  let J' := J.map (Function.Embedding.subtype (fun u => u ∉ I))
  have hG' := hG J' (by simpa only [J', Finset.card_map] using hJs)
  have hsum : (∑ u ∈ J', (nbrOn G K u).card) ≤ t*J.card := by
    calc
      _ ≤ ∑ u ∈ J', t := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
        exact hdeleted u'.val u'.property
      _ = _ := by simp [J', Nat.mul_comm]
  have hb := boundary_loss G J' K
  have he := congrArg Finset.card (boundary_image G I K J)
  simp only [Finset.card_map] at he
  rw [← he] at hb
  have hh : ((boundaryOn G Finset.univ J').card : ℝ) ≤
      ((boundaryOn (graph G I K) Finset.univ J).card : ℝ)+(t : ℝ)*J.card := by
    exact_mod_cast hb.trans (Nat.add_le_add_left hsum _)
  simp only [J', Finset.card_map] at hG' hh
  nlinarith

theorem left_degree (G : BipGraph L R) (I : Finset L) (K : Finset R) (d : ℕ)
    (hd : ∀ u, (nbrOn G Finset.univ u).card ≤ d) (u : {u // u ∉ I}) :
    (nbrOn (graph G I K) Finset.univ u).card ≤ d := by
  rw [P2MBipartiteInducedSubgraph.left_degree]
  exact (Finset.card_le_card (by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩)).trans (hd u.val)

end P2MProofComplexity.P2MBipartiteDeletionExpansion
end

section
-- Inlined Solutions.P2MCompatibleEdgeDeletion

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MCompatibleEdgeDeletion

open PCNonBool P2MCompatibleEdgeNeighborhoods SemAC02.Supplement

variable {L R E : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    [Fintype E] [DecidableEq E]

def Compatible (G : BipGraph L R) (reserved hole : E → R) (A : Finset E) : Prop :=
  (A : Set E).Pairwise (fun e f => Disjoint (family G reserved hole e) (family G reserved hole f))

noncomputable def holes (reserved hole : E → R) (A : Finset E) : Finset R :=
  A.biUnion (fun e => {reserved e, hole e})

theorem mem_family (G : BipGraph L R) (reserved hole : E → R) (e : E) (w : L) :
    w ∈ family G reserved hole e ↔ ∃ v ∈ ({reserved e, hole e} : Finset R), G.Adj w v := by
  simp only [family, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact ⟨reserved e, Or.inl rfl, h⟩
    · exact ⟨hole e, Or.inr rfl, h⟩
  · rintro ⟨v, hv, h⟩
    rcases hv with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h

theorem owner_unique (G : BipGraph L R) (reserved hole : E → R) (A : Finset E)
    (hA : Compatible G reserved hole A) (e : E) (he : e ∈ A) (f : E) (hf : f ∈ A)
    (w : L) (hwe : w ∈ family G reserved hole e) (hwf : w ∈ family G reserved hole f) : e = f := by
  by_contra hne
  exact (Finset.disjoint_left.mp (hA he hf hne) hwe hwf)

theorem row_injective (G : BipGraph L R) (row : E → L) (reserved hole : E → R)
    (hMatched : ∀ e, G.Adj (row e) (reserved e)) (A : Finset E)
    (hA : Compatible G reserved hole A) : Set.InjOn row (A : Set E) := by
  intro e he f hf hrow
  apply owner_unique G reserved hole A hA e he f hf (row e)
  · exact (mem_family G reserved hole e _).mpr ⟨reserved e, by simp, hMatched e⟩
  · exact (mem_family G reserved hole f _).mpr ⟨reserved f, by simp, by rw [hrow]; exact hMatched f⟩

theorem pairwise_holes (G : BipGraph L R) (row : E → L) (reserved hole : E → R)
    (hMatched : ∀ e, G.Adj (row e) (reserved e)) (hEdge : ∀ e, G.Adj (row e) (hole e))
    (A : Finset E) (hA : Compatible G reserved hole A) :
    (A : Set E).Pairwise (fun e f => Disjoint ({reserved e, hole e} : Finset R) {reserved f, hole f}) := by
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  have hadj : G.Adj (row e) v := by
    rcases Finset.mem_insert.mp hve with rfl | hv
    · exact hMatched e
    · rw [Finset.mem_singleton.mp hv]
      exact hEdge e
  have hwe : row e ∈ family G reserved hole e :=
    (mem_family G reserved hole e _).mpr ⟨reserved e, by simp, hMatched e⟩
  have hwf : row e ∈ family G reserved hole f := (mem_family G reserved hole f _).mpr ⟨v, hvf, hadj⟩
  exact hne (owner_unique G reserved hole A hA e he f hf (row e) hwe hwf)

theorem holes_card (G : BipGraph L R) (row : E → L) (reserved hole : E → R)
    (hMatched : ∀ e, G.Adj (row e) (reserved e)) (hEdge : ∀ e, G.Adj (row e) (hole e))
    (hne : ∀ e, reserved e ≠ hole e) (A : Finset E) (hA : Compatible G reserved hole A) :
    (holes reserved hole A).card = 2*A.card := by
  classical
  rw [holes, Finset.card_biUnion (pairwise_holes G row reserved hole hMatched hEdge A hA)]
  simp [hne, Nat.mul_comm]

theorem deleted_neighbors (G : BipGraph L R) (reserved hole : E → R)
    (A : Finset E) (hA : Compatible G reserved hole A) (w : L) :
    (nbrOn G (holes reserved hole A) w).card ≤ 2 := by
  classical
  by_cases hne : (nbrOn G (holes reserved hole A) w).Nonempty
  · obtain ⟨v, hv⟩ := hne
    have hv' := Finset.mem_filter.mp hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv'.1
    have hwe : w ∈ family G reserved hole e := (mem_family G reserved hole e w).mpr ⟨v, hve, hv'.2⟩
    have hsub : nbrOn G (holes reserved hole A) w ⊆ {reserved e, hole e} := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      obtain ⟨f, hf, hzf⟩ := Finset.mem_biUnion.mp hz'.1
      have hwf := (mem_family G reserved hole f w).mpr ⟨z, hzf, hz'.2⟩
      have hef := owner_unique G reserved hole A hA e he f hf w hwe hwf
      rwa [← hef] at hzf
    exact (Finset.card_le_card hsub).trans (by exact Finset.card_insert_le _ _)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp

theorem expansion (G : BipGraph L R) (row : E → L) (reserved hole : E → R)
    (A : Finset E) (hA : Compatible G reserved hole A) (s δ : ℝ) (hG : IsBdryExp G s δ) :
    IsBdryExp (P2MBipartiteInducedSubgraph.graph G (A.image row) (holes reserved hole A)) s (δ-2) := by
  exact P2MBipartiteDeletionExpansion.expansion G (A.image row) (holes reserved hole A) s δ hG 2
    (fun w _ => deleted_neighbors G reserved hole A hA w)

end P2MProofComplexity.P2MCompatibleEdgeDeletion
end

section
-- Inlined Solutions.P2MFunctionalPHPCompatibleSets

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MFunctionalPHPCompatibleSets

open P2MFunctionalPHPMatchingVariables P2MProofComplexity

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def row (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Selected G μ) : L := e.val.val.1
def hole (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Selected G μ) : R := e.val.val.2

def freeEmbedding (G : PCNonBool.BipGraph L R) (μ : R → L) : Selected G μ ↪ Free G μ where
  toFun e := ⟨e.val, e.property.1⟩
  inj' := by intro e f h; exact Subtype.ext (congrArg (fun x : Free G μ => x.val) h)

abbrev Compatible (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ)) :=
  P2MCompatibleEdgeDeletion.Compatible (addMatching G μ) (reserved G μ) (hole G μ) A

noncomputable def rows (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ)) : Finset L :=
  A.image (row G μ)

noncomputable def holes (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ)) : Finset R :=
  P2MCompatibleEdgeDeletion.holes (reserved G μ) (hole G μ) A

theorem matched (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Selected G μ) :
    (addMatching G μ).Adj (row G μ e) (reserved G μ e) := Or.inr (reserved_spec G μ e)

theorem edge (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Selected G μ) :
    (addMatching G μ).Adj (row G μ e) (hole G μ e) := e.val.property

theorem reserved_ne (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Selected G μ) :
    reserved G μ e ≠ hole G μ e := by
  intro he
  exact e.property.1 ((reserved_spec G μ e).symm.trans (congrArg μ he))

theorem row_injective (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (hA : Compatible G μ A) : Set.InjOn (row G μ) (A : Set (Selected G μ)) :=
  P2MCompatibleEdgeDeletion.row_injective _ _ _ _ (matched G μ) A hA

theorem rows_card (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (hA : Compatible G μ A) : (rows G μ A).card = A.card :=
  Finset.card_image_iff.mpr (row_injective G μ A hA)

theorem holes_card (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (hA : Compatible G μ A) : (holes G μ A).card = 2*A.card :=
  P2MCompatibleEdgeDeletion.holes_card _ _ _ _ (matched G μ) (edge G μ) (reserved_ne G μ) A hA

theorem expansion (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (hA : Compatible G μ A) (s δ : ℝ) (hG : IsBdryExp (addMatching G μ) s δ) :
    IsBdryExp (P2MBipartiteInducedSubgraph.graph (addMatching G μ) (rows G μ A) (holes G μ A)) s (δ-2) :=
  P2MCompatibleEdgeDeletion.expansion _ _ _ _ A hA s δ hG

theorem compatible_iff_good (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ)) :
    Compatible G μ A ↔ P2MSeparatedSetCounting.Good
      (P2MCompatibleFamilyCounting.conflicts (P2MCompatibleEdgeNeighborhoods.family (addMatching G μ)
        (reserved G μ) (hole G μ))) A := by
  constructor
  · intro hA e he f hf hne hbad
    exact (P2MCompatibleFamilyCounting.mem_conflicts _ e f).mp hbad (hA he hf hne)
  · intro hA e he f hf hne
    by_contra hbad
    exact hA e he f hf hne ((P2MCompatibleFamilyCounting.mem_conflicts _ e f).mpr hbad)

theorem count (G : PCNonBool.BipGraph L R) (μ : R → L)
    (dL dR : ℕ) (hL : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ dL)
    (hR : ∀ v, P2MCleaningDegreeReduction.rightDegree (addMatching G μ) v ≤ dR) (k : ℕ) :
    (Fintype.card (Selected G μ)-(2*dR*dL*(dR+dL))*(k-1))^k ≤
      k.factorial*(P2MSeparatedSetCounting.sets
        (P2MCompatibleFamilyCounting.conflicts (P2MCompatibleEdgeNeighborhoods.family (addMatching G μ)
          (reserved G μ) (hole G μ))) k).card := by
  apply (P2MCompatibleEdgeNeighborhoods.count (addMatching G μ) μ (row G μ) (hole G μ) (reserved G μ)
    (by intro e f hr hh; exact Subtype.ext (Subtype.ext (Prod.ext hr hh)))
    (edge G μ) (reserved_spec G μ) (matched G μ) dL dR hL hR k).2

end SemAC02.Supplement.P2MFunctionalPHPCompatibleSets
end

section
-- Inlined Solutions.CoveredRepresentation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement

/-- A variable may belong to several right-hand clusters, as in the
Mikša--Nordström treatment of functional PHP. -/
structure P2MCoveredRep (σ L R : Type) where
  F0 : Set (MvPolynomial σ (ZMod 2))
  Fu : L → Set (MvPolynomial σ (ZMod 2))
  cover : σ → Finset R

namespace P2MCoveredRep

open MvPolynomial

variable {σ L R : Type}

def axioms (P : P2MCoveredRep σ L R) : Set (MvPolynomial σ (ZMod 2)) :=
  P.F0 ∪ {p | ∃ u, p ∈ P.Fu u}

def axiomsOn (P : P2MCoveredRep σ L R) (J : Finset L) : Set (MvPolynomial σ (ZMod 2)) :=
  P.F0 ∪ {p | ∃ u ∈ J, p ∈ P.Fu u}

noncomputable def graph [DecidableEq σ] (P : P2MCoveredRep σ L R) : PCNonBool.BipGraph L R :=
  open Classical in {Adj := fun u v => ∃ p ∈ P.Fu u, ∃ x ∈ p.vars, v ∈ P.cover x}

def clusters [DecidableEq R] (P : P2MCoveredRep σ L R) (t : Finset σ) : Finset R :=
  t.biUnion P.cover

theorem mem_clusters [DecidableEq R] (P : P2MCoveredRep σ L R) (t : Finset σ) (v : R) :
    v ∈ P.clusters t ↔ ∃ x ∈ t, v ∈ P.cover x := Finset.mem_biUnion

theorem clusters_mono [DecidableEq R] (P : P2MCoveredRep σ L R)
    {t u : Finset σ} (h : t ⊆ u) : P.clusters t ⊆ P.clusters u := by
  intro v hv
  obtain ⟨x, hx, hv⟩ := (mem_clusters P t v).mp hv
  exact (mem_clusters P u v).mpr ⟨x, h hx, hv⟩

theorem clusters_union [DecidableEq σ] [DecidableEq R] (P : P2MCoveredRep σ L R) (t u : Finset σ) :
    P.clusters (t ∪ u) = P.clusters t ∪ P.clusters u := by
  ext v
  simp only [mem_clusters, Finset.mem_union]
  aesop

theorem clusters_card [DecidableEq R] (P : P2MCoveredRep σ L R) (d : ℕ)
    (hd : ∀ x, (P.cover x).card ≤ d) (t : Finset σ) : (P.clusters t).card ≤ d*t.card := by
  calc
    _ ≤ ∑ x ∈ t, (P.cover x).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ t, d := Finset.sum_le_sum (fun x _ => hd x)
    _ = _ := by simp [Nat.mul_comm]

theorem clusters_card_real [DecidableEq R] (P : P2MCoveredRep σ L R) (d : ℕ)
    (hd : ∀ x, (P.cover x).card ≤ d) (t : Finset σ) :
    ((P.clusters t).card : ℝ) ≤ (d : ℝ)*t.card := by
  exact_mod_cast clusters_card P d hd t

theorem clusters_insert_bound [DecidableEq σ] [DecidableEq R]
    (P : P2MCoveredRep σ L R) (d : ℕ) (hd : ∀ x, (P.cover x).card ≤ d) (t : Finset σ) (x : σ) :
    ((P.clusters (insert x t)).card : ℝ) ≤ (d : ℝ)*((t.card : ℝ)+1) := by
  have hh := (clusters_card P d hd (insert x t)).trans (Nat.mul_le_mul_left d (Finset.card_insert_le x t))
  exact_mod_cast hh

noncomputable def substCluster (P : P2MCoveredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) : MvPolynomial σ (ZMod 2) :=
  open Classical in aeval (fun x => if v ∈ P.cover x then C (α x) else X x) p

def IsRespectful [DecidableEq σ] [Fintype L] [DecidableEq L] (P : P2MCoveredRep σ L R) : Prop :=
  ∀ (J : Finset L) (v : R) (u : L),
    J.filter (fun u' => P.graph.Adj u' v) = {u} →
    ∃ α : σ → ZMod 2,
      (∀ p ∈ P.Fu u, ∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α p) = 0) ∧
      ∀ g ∈ P.F0, (∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α g) = 0) ∨
        (∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α g) = eval (toF2 y) g)

noncomputable def expOp [DecidableEq σ] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (t : Finset σ) : MvPolynomial σ (ZMod 2) :=
  nf m (P.axiomsOn (supS P.graph s (P.clusters t))) (AC02Frege.xMon t)

end P2MCoveredRep
end SemAC02.Supplement
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
-- Inlined Solutions.P2MBooleanVariableProducts

namespace AC02Frege.P2MBooleanVariableProducts

open MvPolynomial AC02Frege.P2MBooleanAlgebra

theorem monomial_insert {σ : Type} [Finite σ] [DecidableEq σ] (x : σ) (t : Finset σ) :
    ML (X x*xMon t)=xMon (insert x t) := by
  apply multilinear_ext (ml_multilinear _) (xMon_multilinear _)
  intro y
  simp only [eval_ml,map_mul,eval_X,xMon_eval]
  by_cases hx : x∈t
  · rw [Finset.insert_eq_of_mem hx]
    have he : t=insert x (t.erase x) := (Finset.insert_erase hx).symm
    rw [he,Finset.prod_insert (Finset.notMem_erase x t)]
    have hy : y x*y x=y x := by
      rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (y x) with h | h <;> simp [h]
    rw [←mul_assoc,hy]
  · rw [Finset.prod_insert hx]

end AC02Frege.P2MBooleanVariableProducts
end

section
-- Inlined Solutions.P2MFunctionalPHPCoveredRepresentation

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPCoveredRepresentation

open MvPolynomial AC02Frege LiftSAParity

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

noncomputable def rowVariables (G : PCNonBool.BipGraph L R) (u : L) : Finset (Edge G) :=
  (PCNonBool.nbrOn G Finset.univ u).attach.image
    (fun v => ⟨(u, v.val), by simpa [PCNonBool.nbrOn] using v.property⟩)

noncomputable def rowClause (G : PCNonBool.BipGraph L R) (u : L) : Clause (Edge G) :=
  (rowVariables G u).image (fun e => (e, true))

def Conflict {G : PCNonBool.BipGraph L R} (e f : Edge G) : Prop :=
  e ≠ f ∧ (e.val.1 = f.val.1 ∨ e.val.2 = f.val.2)

def background (G : PCNonBool.BipGraph L R) : Set (MvPolynomial (Edge G) (ZMod 2)) :=
  {p | ∃ e f : Edge G, Conflict e f ∧ p = X e*X f}

noncomputable def representation (G : PCNonBool.BipGraph L R) : P2MCoveredRep (Edge G) L R where
  F0 := background G
  Fu := fun u => {P2MCNFExpansionPolynomials.polynomial (rowClause G u)}
  cover := fun e => PCNonBool.nbrOn G Finset.univ e.val.1

theorem mem_rowVariables (G : PCNonBool.BipGraph L R) (u : L) (e : Edge G) :
    e ∈ rowVariables G u ↔ e.val.1 = u := by
  constructor
  · intro he
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp he
    exact (congrArg (fun e : Edge G => e.val.1) he).symm
  · intro he
    rcases e with ⟨⟨a, b⟩, hab⟩
    dsimp only at he
    subst a
    have hb : b ∈ PCNonBool.nbrOn G Finset.univ u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
    exact Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_attach _ _, rfl⟩

theorem row_card (G : PCNonBool.BipGraph L R) (u : L) :
    (rowVariables G u).card = (PCNonBool.nbrOn G Finset.univ u).card := by
  unfold rowVariables
  rw [Finset.card_image_of_injective]
  · simp
  · intro v w he
    exact Subtype.ext (congrArg (fun e : Edge G => e.val.2) he)

theorem consistent (G : PCNonBool.BipGraph L R) (u : L) :
    P2MCNFExpansionPolynomials.Consistent (rowClause G u) := by
  intro e he
  obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp he.2
  have hh := congrArg Prod.snd heq
  cases hh

theorem row_vars (G : PCNonBool.BipGraph L R) (u : L) :
    (P2MCNFExpansionPolynomials.polynomial (rowClause G u)).vars = rowVariables G u := by
  rw [P2MCNFExpansionPolynomials.vars_eq _ (consistent G u), rowClause, Finset.image_image]
  simp [Function.comp_def]

theorem row_degree (G : PCNonBool.BipGraph L R) (u : L) :
    (P2MCNFExpansionPolynomials.polynomial (rowClause G u)).totalDegree ≤
      (PCNonBool.nbrOn G Finset.univ u).card := by
  apply (P2MCNFExpansionPolynomials.degree _).trans
  exact Finset.card_image_le.trans (row_card G u).le

theorem graph_iff (G : PCNonBool.BipGraph L R) (u : L) (v : R) :
    (representation G).graph.Adj u v ↔ G.Adj u v := by
  classical
  constructor
  · rintro ⟨p, hp, e, he, hv⟩
    have hp' : p = P2MCNFExpansionPolynomials.polynomial (rowClause G u) := Set.mem_singleton_iff.mp hp
    rw [hp', row_vars] at he
    have he' := (mem_rowVariables G u e).mp he
    have hv' : G.Adj e.val.1 v := (Finset.mem_filter.mp hv).2
    rwa [he'] at hv'
  · intro huv
    let e : Edge G := ⟨(u, v), huv⟩
    refine ⟨P2MCNFExpansionPolynomials.polynomial (rowClause G u), Set.mem_singleton _, e, ?_, ?_⟩
    · rw [row_vars]
      exact (mem_rowVariables G u e).mpr rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩

theorem graph_eq (G : PCNonBool.BipGraph L R) : (representation G).graph = G := by
  have extG (G H : PCNonBool.BipGraph L R) (he : G.Adj = H.Adj) : G = H := by
    cases G with
    | mk a =>
      cases H with
      | mk b =>
        dsimp only at he
        cases he
        congr
  apply extG
  funext u v
  exact propext (graph_iff G u v)

theorem overlap (G : PCNonBool.BipGraph L R) (d : ℕ)
    (hd : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ d) :
    ∀ e, ((representation G).cover e).card ≤ d := fun e => hd e.val.1

theorem background_multilinear (G : PCNonBool.BipGraph L R) (p : MvPolynomial (Edge G) (ZMod 2))
    (hp : p ∈ background G) : IsMultilinear p := by
  classical
  obtain ⟨e, f, hconflict, rfl⟩ := hp
  have hne := hconflict.1
  have he : X e*X f = xMon ({e, f} : Finset (Edge G)) := by simp [xMon, hne]
  rw [he]
  exact AC02Frege.P2MBooleanAlgebra.xMon_multilinear _

theorem multilinear (G : PCNonBool.BipGraph L R) :
    ∀ p ∈ (representation G).axioms, IsMultilinear p := by
  rintro p (hp | ⟨u, hp⟩)
  · exact background_multilinear G p hp
  · have he : p = P2MCNFExpansionPolynomials.polynomial (rowClause G u) := Set.mem_singleton_iff.mp hp
    rw [he]
    exact P2MCNFExpansionPolynomials.multilinear _

theorem degrees (G : PCNonBool.BipGraph L R) (d : ℕ)
    (hd : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ d) :
    ∀ p ∈ (representation G).axioms, p.totalDegree ≤ max 2 d := by
  rintro p (hp | ⟨u, hp⟩)
  · obtain ⟨e, f, hconflict, rfl⟩ := hp
    exact (totalDegree_mul (X e) (X f)).trans (by simp)
  · have he : p = P2MCNFExpansionPolynomials.polynomial (rowClause G u) := Set.mem_singleton_iff.mp hp
    rw [he]
    exact ((row_degree G u).trans (hd u)).trans (le_max_right _ _)

theorem raw_row (G : PCNonBool.BipGraph L R) (u : L) :
    clausePolyF (F:=ZMod 2) (rowClause G u) =
      ∏ v ∈ (PCNonBool.nbrOn G Finset.univ u).attach,
        (1-xE G u v.val (by simpa [PCNonBool.nbrOn] using v.property)) := by
  classical
  unfold clausePolyF rowClause
  rw [Finset.prod_image (by intro a ha b hb he; exact congrArg Prod.fst he)]
  simp only [litPolyF, ite_true]
  unfold rowVariables
  rw [Finset.prod_image]
  · rfl
  · intro a ha b hb he
    exact Subtype.ext (congrArg (fun e : Edge G => e.val.2) he)

end SemAC02.Supplement.P2MFunctionalPHPCoveredRepresentation
end

section
-- Inlined Solutions.P2MOrthogonalProduct

namespace P2MProofComplexity.P2MOrthogonalProduct

theorem prod_one_add {I F : Type} [DecidableEq I] [CommRing F]
    (S : Finset I) (a : I → F)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → a i*a j = 0) :
    (∏ i ∈ S, (1+a i)) = 1+∑ i ∈ S, a i := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      ih (fun j hj k hk hne => horth j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)]
    have hcross : a i*(∑ j ∈ S, a j) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by intro he; subst j; exact hi hj)
    calc
      _ = 1+(a i+∑ j ∈ S, a j)+a i*(∑ j ∈ S, a j) := by ring
      _ = _ := by rw [hcross, add_zero]

end P2MProofComplexity.P2MOrthogonalProduct
end

section
-- Inlined Solutions.P2MFunctionalPHPRowSemantics

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPRowSemantics

open MvPolynomial AC02Frege LiftSAParity P2MFunctionalPHPCoveredRepresentation

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem raw_row_variables (G : PCNonBool.BipGraph L R) (u : L) :
    clausePolyF (F:=ZMod 2) (rowClause G u) = ∏ e ∈ rowVariables G u, (1-X e) := by
  classical
  unfold clausePolyF rowClause
  rw [Finset.prod_image (by intro a ha b hb he; exact congrArg Prod.fst he)]
  simp only [litPolyF, ite_true]

theorem pigeon_axiom (G : PCNonBool.BipGraph L R) (u : L) :
    clausePolyF (F:=ZMod 2) (rowClause G u) ∈ fphpG G := by
  left
  refine ⟨u, ?_⟩
  rw [raw_row]
  simp only [CharTwo.sub_eq_add]

theorem conflict_axiom (G : PCNonBool.BipGraph L R) (e f : Edge G) (hconflict : Conflict e f) :
    (X e*X f : MvPolynomial (Edge G) (ZMod 2)) ∈ fphpG G := by
  rcases hconflict.2 with hrow | hhole
  · have hf : G.Adj e.val.1 f.val.2 := by rw [hrow]; exact f.property
    have hfe : (⟨(e.val.1, f.val.2), hf⟩ : Edge G) = f := Subtype.ext (Prod.ext hrow rfl)
    have hne : e.val.2 ≠ f.val.2 := fun he => hconflict.1 (Subtype.ext (Prod.ext hrow he))
    right; left
    refine ⟨e.val.1, e.val.2, f.val.2, e.property, hf, hne, ?_⟩
    simp only [xE]
    rw [hfe]
  · have hf : G.Adj f.val.1 e.val.2 := by rw [hhole]; exact f.property
    have hfe : (⟨(f.val.1, e.val.2), hf⟩ : Edge G) = f := Subtype.ext (Prod.ext rfl hhole)
    have hne : e.val.1 ≠ f.val.1 := fun he => hconflict.1 (Subtype.ext (Prod.ext he hhole))
    right; right
    refine ⟨e.val.1, f.val.1, e.val.2, e.property, hf, hne, ?_⟩
    simp only [xE]
    rw [hfe]

theorem pigeon_vars (G : PCNonBool.BipGraph L R) (u : L) :
    (clausePolyF (F:=ZMod 2) (rowClause G u)).vars ⊆ rowVariables G u := by
  classical
  intro e he
  rw [raw_row_variables] at he
  obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.mp (vars_prod _ he)
  have heq : e = f := by
    have hef' : e ∈ (1+X f : MvPolynomial (Edge G) (ZMod 2)).vars := by
      simpa only [CharTwo.sub_eq_add] using hef
    simpa using (vars_add_subset (1 : MvPolynomial (Edge G) (ZMod 2)) (X f) hef')
  rwa [heq]

theorem pigeon_degree (G : PCNonBool.BipGraph L R) (u : L) :
    (clausePolyF (F:=ZMod 2) (rowClause G u)).totalDegree ≤ (PCNonBool.nbrOn G Finset.univ u).card := by
  rw [raw_row_variables]
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ e ∈ rowVariables G u, (1-X e : MvPolynomial (Edge G) (ZMod 2)).totalDegree) ≤
        ∑ e ∈ rowVariables G u, 1 := by
      apply Finset.sum_le_sum
      intro e he
      exact (totalDegree_sub _ _).trans (by simp)
    _ = (rowVariables G u).card := by simp
    _ = _ := row_card G u

theorem quadratic_vars (G : PCNonBool.BipGraph L R) (e f : Edge G) :
    (X e*X f : MvPolynomial (Edge G) (ZMod 2)).vars ⊆ {e, f} := by
  simpa using vars_mul (X e : MvPolynomial (Edge G) (ZMod 2)) (X f)

theorem row_sum (G : PCNonBool.BipGraph L R) (u : L) (x : Edge G → ZMod 2)
    (hP : eval x (clausePolyF (rowClause G u)) = 0)
    (hF : ∀ e ∈ rowVariables G u, ∀ f ∈ rowVariables G u, e ≠ f → x e*x f = 0) :
    1+(∑ e ∈ rowVariables G u, x e) = 0 := by
  have he : eval x (clausePolyF (F:=ZMod 2) (rowClause G u)) = ∏ e ∈ rowVariables G u, (1+x e) := by
    rw [raw_row_variables, map_prod]
    simp only [CharTwo.sub_eq_add, map_add, map_one, eval_X]
  rw [he, P2MProofComplexity.P2MOrthogonalProduct.prod_one_add _ _ hF] at hP
  exact hP

noncomputable def rowSupport (G : PCNonBool.BipGraph L R) (U : Finset L) : Finset (Edge G) :=
  U.biUnion (rowVariables G)

theorem mem_rowSupport (G : PCNonBool.BipGraph L R) (U : Finset L) (e : Edge G) :
    e ∈ rowSupport G U ↔ e.val.1 ∈ U := by
  simp only [rowSupport, Finset.mem_biUnion, mem_rowVariables]
  constructor
  · rintro ⟨u, hu, he⟩
    rwa [he]
  · intro he
    exact ⟨e.val.1, he, rfl⟩

theorem rowSupport_card (G : PCNonBool.BipGraph L R) (U : Finset L) (d : ℕ)
    (hd : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ d) :
    (rowSupport G U).card ≤ d*U.card := by
  calc
    _ ≤ ∑ u ∈ U, (rowVariables G u).card := Finset.card_biUnion_le
    _ ≤ ∑ u ∈ U, d := Finset.sum_le_sum (fun u _ => by rw [row_card]; exact hd u)
    _ = _ := by simp [Nat.mul_comm]

theorem all_degree (G : PCNonBool.BipGraph L R) (d : ℕ)
    (hd : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ d) :
    ∀ p ∈ fphpG G, p.totalDegree ≤ max 2 d := by
  rintro p (⟨u, rfl⟩ | ⟨u, v, v', h, h', hne, rfl⟩ | ⟨u, u', v, h, h', hne, rfl⟩)
  · have he : (∏ v ∈ (PCNonBool.nbrOn G Finset.univ u).attach,
        (1+xE G u v.val (by simpa [PCNonBool.nbrOn] using v.property))) =
        clausePolyF (F:=ZMod 2) (rowClause G u) := by
      rw [raw_row]
      simp only [CharTwo.sub_eq_add]
    rw [he]
    exact ((pigeon_degree G u).trans (hd u)).trans (le_max_right _ _)
  · exact (totalDegree_mul _ _).trans (by simp [xE])
  · exact (totalDegree_mul _ _).trans (by simp [xE])

theorem local_row_sum (G : PCNonBool.BipGraph L R) (U : Finset L) (x : Edge G → ZMod 2)
    (hzero : ∀ p ∈ fphpG G, p.vars ⊆ rowSupport G U → eval x p = 0) :
    ∀ u ∈ U, 1+(∑ e ∈ rowVariables G u, x e) = 0 := by
  intro u hu
  have hrow : rowVariables G u ⊆ rowSupport G U := fun e he => Finset.mem_biUnion.mpr ⟨u, hu, he⟩
  apply row_sum G u x (hzero _ (pigeon_axiom G u) ((pigeon_vars G u).trans hrow))
  intro e he f hf hne
  have herow := (mem_rowVariables G u e).mp he
  have hfrow := (mem_rowVariables G u f).mp hf
  have hconflict : Conflict e f := ⟨hne, Or.inl (herow.trans hfrow.symm)⟩
  have hvars : (X e*X f : MvPolynomial (Edge G) (ZMod 2)).vars ⊆ rowSupport G U :=
    (quadratic_vars G e f).trans (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hrow he, hrow hf⟩)
  have hh := hzero _ (conflict_axiom G e f hconflict) hvars
  simpa only [map_mul, eval_X] using hh

theorem quadratic_rows (G : PCNonBool.BipGraph L R) (e f : Edge G) :
    (X e*X f : MvPolynomial (Edge G) (ZMod 2)).vars ⊆ rowSupport G {e.val.1, f.val.1} := by
  classical
  apply (quadratic_vars G e f).trans
  intro g hg
  rcases Finset.mem_insert.mp hg with rfl | hg
  · exact (mem_rowSupport _ _ _).mpr (by simp)
  · have he := Finset.mem_singleton.mp hg
    subst g
    exact (mem_rowSupport _ _ _).mpr (by simp)

theorem axiom_rows (G : PCNonBool.BipGraph L R) (p : MvPolynomial (Edge G) (ZMod 2))
    (hp : p ∈ fphpG G) :
    ∃ U : Finset L, U.card ≤ 2 ∧ p.vars ⊆ rowSupport G U := by
  classical
  rcases hp with ⟨u, rfl⟩ | ⟨u, v, v', h, h', hne, rfl⟩ | ⟨u, u', v, h, h', hne, rfl⟩
  · refine ⟨{u}, by simp, ?_⟩
    have he : (∏ v ∈ (PCNonBool.nbrOn G Finset.univ u).attach,
        (1+xE G u v.val (by simpa [PCNonBool.nbrOn] using v.property))) =
        clausePolyF (F:=ZMod 2) (rowClause G u) := by
      rw [raw_row]
      simp only [CharTwo.sub_eq_add]
    rw [he]
    exact (pigeon_vars G u).trans (by intro e he; exact (mem_rowSupport _ _ _).mpr (by simpa [mem_rowVariables] using he))
  · refine ⟨{u}, by simp, ?_⟩
    simpa only [xE, Finset.insert_eq_of_mem (Finset.mem_singleton_self u)] using
      quadratic_rows G ⟨(u, v), h⟩ ⟨(u, v'), h'⟩
  · refine ⟨{u, u'}, by exact Finset.card_insert_le _ _, ?_⟩
    simpa only [xE] using quadratic_rows G ⟨(u, v), h⟩ ⟨(u', v), h'⟩

end SemAC02.Supplement.P2MFunctionalPHPRowSemantics
end

section
-- Inlined Solutions.PCOperations

open MvPolynomial

namespace AC02Frege.P2MSupport

theorem derivation_append {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K))
    {π ρ : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π)
    (hρ : PCNonBool.IsDerivation red P ρ) :
    PCNonBool.IsDerivation red P (π ++ ρ) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left
      simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    have hk' : k < ρ.length := by simp only [List.length_append] at hk; omega
    have hget (t : ℕ) (ht : t < ρ.length) :
        (π ++ ρ)[π.length + t]'(by simp only [List.length_append]; omega) = ρ[t] := by
      rw [List.getElem_append_right (Nat.le_add_right π.length t)]
      simp only [Nat.add_sub_cancel_left]
    rcases hρ k hk' with ha | hc | hm
    · left
      obtain ⟨a, ha, c, hac⟩ := ha
      exact ⟨a, ha, c, (hget k hk').trans hac⟩
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨π.length + i, π.length + j, by omega, by omega, a, b, ?_⟩
      rw [hget k hk', hget i (hi.trans hk'), hget j (hj.trans hk')]
      exact hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨π.length + i, by omega, v, ?_⟩
      rw [hget k hk', hget i (hi.trans hk')]
      exact hiv

theorem derivation_snoc {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K)) {π : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π) (p : MvPolynomial σ K)
    (hp :
      (∃ a ∈ P, ∃ c : K, p = c • red a) ∨
      (∃ (i j : ℕ) (hi : i < π.length) (hj : j < π.length) (a b : K),
        p = a • π[i] + b • π[j]) ∨
      (∃ (i : ℕ) (hi : i < π.length) (v : σ), p = red (X v * π[i]))) :
    PCNonBool.IsDerivation red P (π ++ [p]) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left; simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · have heq : k = π.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    have hlast : (π ++ [p])[π.length] = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    rcases hp with ha | hc | hm
    · left; simpa only [hlast] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [hlast, List.getElem_append_left hi, List.getElem_append_left hj] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [hlast, List.getElem_append_left hi] using hiv

theorem pc_zero {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    PCDerivable F D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {F : LiftSAParity.CNF (Fin n)} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) (c : ZMod 2) :
    PCDerivable F D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero F D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : PCDerivable F D p) (hq : PCDerivable F D q) :
    PCDerivable F D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show PCDerivable F D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (p * X v) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [zero_mul]; exact pc_zero F D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [p * X v], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by simp only [hpi, LinearMap.id_apply, mul_comm]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = p * X v := List.mem_singleton.mp hq
      subst q
      exact (totalDegree_mul p (X v)).trans (by simpa only [totalDegree_X] using hdeg)

theorem pc_axiom {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ pcAxioms F)
    (hdeg : p.totalDegree ≤ D) : PCDerivable F D p := by
  refine Or.inr ⟨[p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

end AC02Frege.P2MSupport
end

section
-- Inlined Solutions.P2MBooleanPC

open MvPolynomial AC02Frege
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MBooleanPC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q.totalDegree ≤ D) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Derivable P D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) (c : ZMod 2) :
    Derivable P D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero P D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : Derivable P D p) (hq : Derivable P D q) :
    Derivable P D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show Derivable P D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    Derivable P D (ML (X v * p)) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [mul_zero, map_zero]; exact pc_zero P D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = ML (X v * p) := List.mem_singleton.mp hq
      subst q
      exact (ml_totalDegree_le _).trans ((totalDegree_mul (X v) p).trans (by simpa only [totalDegree_X, Nat.add_comm] using hdeg))

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P)
    (hdeg : (ML p).totalDegree ≤ D) : Derivable P D (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

theorem pc_mono {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D E : ℕ}
    (hDE : D ≤ E) {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) :
    Derivable P E p := by
  rcases hp with h | ⟨π, hπ, hdeg, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨π, hπ, fun q hq => (hdeg q hq).trans hDE, hp⟩

noncomputable def consequenceSpace {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := {p | Derivable P D p}
  zero_mem' := pc_zero P D
  add_mem' := pc_add P D
  smul_mem' := fun a _ hp => pc_smul P D hp a

end SemAC02.P2MBooleanPC
end

section
-- Inlined Solutions.P2MRelativePCFinite

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePCFinite

def Derivable {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (p : MvPolynomial V (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial V (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {V : Type} {P : Set (MvPolynomial V (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))}
    {p : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    {p : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
    Derivable P U (c • p) := by
  rcases hp with rfl | ⟨π,hπ,hmem,hp⟩
  · simp only [smul_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; left
    exact ⟨i,i,hi,hi,c,0,by simp only [hpi,zero_smul,add_zero]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmem q hq
    · have he : q = c • p := List.mem_singleton.mp hq
      rw [he]
      exact U.smul_mem c (hmem p hp)

theorem pc_add {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    {p q : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
    Derivable P U (p+q) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ,hρ,hρmem,hq⟩
  · simpa only [add_zero] using (show Derivable P U p from Or.inr ⟨π,hπ,hπmem,hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j,hj,hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p+q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i,j,hi,hj,1,1,by simp only [hpi,hqj,one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπmem r hr
      · exact hρmem r hr
    · have he : r = p+q := List.mem_singleton.mp hr
      rw [he]
      exact U.add_mem (hπmem p hp) (hρmem q hq)

theorem pc_mul_X {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    {p : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) (v : V)
    (hmem : ML (X v * p) ∈ U) : Derivable P U (ML (X v * p)) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simp only [mul_zero,map_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i,hi,v,by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπmem q hq
    · rwa [List.mem_singleton.mp hq]

theorem pc_axiom {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.P2MRelativePCFinite
end

section
-- Inlined Solutions.P2MBooleanDegreeSpaces

open MvPolynomial AC02Frege AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MBooleanDegreeSpaces

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
  rw [he,mem_light_iff]

end SemAC02.P2MBooleanDegreeSpaces
end

section
-- Inlined Solutions.P2MRelativePCRenaming

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MRelativePCRenaming

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces

variable {V W : Type} [Finite V] [Finite W]

/-- Renaming followed by reduction is a homomorphism of Boolean polynomial algebras. -/
noncomputable def transport (f : V → W) :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial W (ZMod 2) :=
  ML.comp (rename f).toLinearMap

theorem transport_ml (f : V → W) (p : MvPolynomial V (ZMod 2)) :
    transport f (ML p) = transport f p := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [transport, LinearMap.comp_apply, AlgHom.toLinearMap_apply, eval_ml, eval_rename]

theorem transport_mul_X (f : V → W) (v : V) (p : MvPolynomial V (ZMod 2)) :
    transport f (ML (X v*p)) = ML (X (f v)*transport f p) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [transport, LinearMap.comp_apply, AlgHom.toLinearMap_apply, eval_ml,
    eval_rename, map_mul, eval_X, Function.comp_apply]

theorem transport_degree (f : V → W) (p : MvPolynomial V (ZMod 2)) :
    (transport f p).totalDegree ≤ p.totalDegree :=
  (P2MBooleanFlip.ml_totalDegree_le _).trans (totalDegree_rename_le f p)

theorem transport_mem (f : V → W) (B : ℕ) (p : MvPolynomial V (ZMod 2))
    (hp : p.totalDegree ≤ B) : transport f p ∈ Ble W B :=
  (mem_Ble_iff B _).mpr ⟨ml_multilinear _, (transport_degree f p).trans hp⟩

/-- Each substituted axiom may have an independent bounded-degree derivation. These
certificates extend line by line to every derivation from the substituted axioms. -/
theorem derivation (f : V → W) (P : Set (MvPolynomial V (ZMod 2)))
    (Q : Set (MvPolynomial W (ZMod 2))) (B : ℕ)
    (haxiom : ∀ p ∈ P, P2MRelativePCFinite.Derivable Q (Ble W B) (transport f p))
    (π : List (MvPolynomial V (ZMod 2))) (hπ : PCNonBool.IsDerivation ML P π)
    (hdegree : ∀ p ∈ π, p.totalDegree ≤ B) :
    ∀ p ∈ π, P2MRelativePCFinite.Derivable Q (Ble W B) (transport f p) := by
  have hall : ∀ k (hk : k < π.length),
      P2MRelativePCFinite.Derivable Q (Ble W B) (transport f π[k]) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ k hk with ⟨p, hp, a, he⟩ | ⟨i, j, hi, hj, a, b, he⟩ | ⟨i, hi, v, he⟩
      · rw [he, map_smul, transport_ml]
        exact P2MRelativePCFinite.pc_smul Q (Ble W B) (haxiom p hp) a
      · rw [he, map_add, map_smul, map_smul]
        exact P2MRelativePCFinite.pc_add Q (Ble W B)
          (P2MRelativePCFinite.pc_smul Q _ (ih i hi (hi.trans hk)) a)
          (P2MRelativePCFinite.pc_smul Q _ (ih j hj (hj.trans hk)) b)
      · rw [he, transport_mul_X]
        apply P2MRelativePCFinite.pc_mul_X Q (Ble W B) (ih i hi (hi.trans hk)) (f v)
        rw [← transport_mul_X, ← he]
        exact transport_mem f B π[k] (hdegree _ (List.getElem_mem hk))
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
  exact hall k hk

end SemAC02.Supplement.P2MRelativePCRenaming
end

section
-- Inlined Solutions.P2MRelativePCRestriction

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MRelativePCRestriction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces

variable {V W : Type} [Finite V] [Finite W]

/-- Each variable is retained as a target variable or assigned a field constant. -/
noncomputable def leaf (ρ : V → W ⊕ ZMod 2) (v : V) : MvPolynomial W (ZMod 2) :=
  Sum.elim X C (ρ v)

noncomputable def transport (ρ : V → W ⊕ ZMod 2) :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial W (ZMod 2) :=
  ML.comp (bind₁ (leaf ρ)).toLinearMap

theorem transport_multilinear (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (transport ρ p) := ml_multilinear _

theorem evaluation (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial V (ZMod 2)) (x : W → ZMod 2) :
    eval x (transport ρ p) = eval (fun v => eval x (leaf ρ v)) p := by
  change eval x (ML (bind₁ (leaf ρ) p)) = _
  rw [eval_ml]
  exact eval₂Hom_bind₁ _ _ _ _

theorem transport_ml (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial V (ZMod 2)) :
    transport ρ (ML p) = transport ρ p := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  change eval x (transport ρ (ML p)) = eval x (transport ρ p)
  rw [evaluation, evaluation, eval_ml]

theorem transport_mul_X (ρ : V → W ⊕ ZMod 2) (v : V) (p : MvPolynomial V (ZMod 2)) :
    transport ρ (ML (X v*p)) = ML (leaf ρ v*transport ρ p) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  change eval x (transport ρ (ML (X v*p))) = eval x (ML (leaf ρ v*transport ρ p))
  rw [evaluation, eval_ml, map_mul, eval_X, eval_ml, map_mul, evaluation]

theorem transport_degree (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial V (ZMod 2)) :
    (transport ρ p).totalDegree ≤ p.totalDegree := by
  apply (P2MBooleanFlip.ml_totalDegree_le _).trans
  apply P2MBooleanFlip.bind_linear_totalDegree_le
  intro v
  unfold leaf
  cases ρ v <;> simp

theorem transport_mem (ρ : V → W ⊕ ZMod 2) (B : ℕ) (p : MvPolynomial V (ZMod 2))
    (hp : p.totalDegree ≤ B) : transport ρ p ∈ Ble W B :=
  (mem_Ble_iff B _).mpr ⟨ml_multilinear _, (transport_degree ρ p).trans hp⟩

theorem transport_one (ρ : V → W ⊕ ZMod 2) : transport ρ 1 = 1 := by
  change ML (bind₁ (leaf ρ) 1) = 1
  rw [map_one, ml_of_multilinear _ (by simp [IsMultilinear])]

theorem derivation (ρ : V → W ⊕ ZMod 2) (P : Set (MvPolynomial V (ZMod 2)))
    (Q : Set (MvPolynomial W (ZMod 2))) (B : ℕ)
    (haxiom : ∀ p ∈ P, P2MRelativePCFinite.Derivable Q (Ble W B) (transport ρ p))
    (π : List (MvPolynomial V (ZMod 2))) (hπ : PCNonBool.IsDerivation ML P π)
    (hdegree : ∀ p ∈ π, p.totalDegree ≤ B) :
    ∀ p ∈ π, P2MRelativePCFinite.Derivable Q (Ble W B) (transport ρ p) := by
  have hall : ∀ k (hk : k < π.length),
      P2MRelativePCFinite.Derivable Q (Ble W B) (transport ρ π[k]) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ k hk with ⟨p, hp, a, he⟩ | ⟨i, j, hi, hj, a, b, he⟩ | ⟨i, hi, v, he⟩
      · rw [he, map_smul, transport_ml]
        exact P2MRelativePCFinite.pc_smul Q (Ble W B) (haxiom p hp) a
      · rw [he, map_add, map_smul, map_smul]
        exact P2MRelativePCFinite.pc_add Q (Ble W B)
          (P2MRelativePCFinite.pc_smul Q _ (ih i hi (hi.trans hk)) a)
          (P2MRelativePCFinite.pc_smul Q _ (ih j hj (hj.trans hk)) b)
      · have hmem := transport_mem ρ B π[k] (hdegree _ (List.getElem_mem hk))
        rw [he, transport_mul_X] at hmem ⊢
        cases hleaf : ρ v with
        | inl w =>
          simp only [leaf, hleaf, Sum.elim_inl] at hmem ⊢
          exact P2MRelativePCFinite.pc_mul_X Q _ (ih i hi (hi.trans hk)) w hmem
        | inr c =>
          simp only [leaf, hleaf, Sum.elim_inr] at hmem ⊢
          rw [← smul_eq_C_mul, map_smul, ml_of_multilinear _ (transport_multilinear ρ _)]
          exact P2MRelativePCFinite.pc_smul Q _ (ih i hi (hi.trans hk)) c
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
  exact hall k hk

end SemAC02.Supplement.P2MRelativePCRestriction
end

section
-- Inlined Solutions.P2MFPHPPartialMatchingRestriction

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFPHPPartialMatchingRestriction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MFunctionalPHPCoveredRepresentation
open P2MFunctionalPHPRowSemantics P2MProofComplexity.P2MBipartiteInducedSubgraph

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

attribute [local instance] Classical.propDecidable

def edgeEmbedding (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) :
    Edge (graph G I K) ↪ Edge G where
  toFun e := ⟨(e.val.1.val, e.val.2.val), e.property⟩
  inj' := by
    intro e f h
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun e : Edge G => e.val.1) h)
    · exact Subtype.ext (congrArg (fun e : Edge G => e.val.2) h)

noncomputable def restriction (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R)
    (χ : I → R) (e : Edge G) : Edge (graph G I K) ⊕ ZMod 2 :=
  if hu : e.val.1 ∈ I then .inr (if e.val.2 = χ ⟨e.val.1, hu⟩ then 1 else 0)
  else if hv : e.val.2 ∈ K then .inr 0
  else .inl ⟨(⟨e.val.1, hu⟩, ⟨e.val.2, hv⟩), e.property⟩

theorem kept (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (e : Edge (graph G I K)) : restriction G I K χ (edgeEmbedding G I K e) = .inl e := by
  change (if hu : e.val.1.val ∈ I then _ else if hv : e.val.2.val ∈ K then _ else _) = _
  rw [dif_neg e.val.1.property, dif_neg e.val.2.property]
  exact congrArg Sum.inl (Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)))

theorem inl_embedding (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (e : Edge G) (f : Edge (graph G I K)) (h : restriction G I K χ e = .inl f) :
    edgeEmbedding G I K f = e := by
  unfold restriction at h
  split at h
  · cases h
  · split at h
    · cases h
    · have hh := Sum.inl.inj h
      rw [← hh]
      exact Subtype.ext rfl

theorem row_image (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R)
    (u : {u // u ∉ I}) :
    (rowVariables (graph G I K) u).map (edgeEmbedding G I K) =
      (rowVariables G u.val).filter (fun e => e.val.2 ∉ K) := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_filter.mpr ⟨(mem_rowVariables _ _ _).mpr
      (congrArg Subtype.val ((mem_rowVariables _ _ _).mp hf)), f.val.2.property⟩
  · intro he
    obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
    have hu : e.val.1 ∉ I := by rw [(mem_rowVariables _ _ _).mp he]; exact u.property
    let f : Edge (graph G I K) := ⟨(⟨e.val.1, hu⟩, ⟨e.val.2, hv⟩), e.property⟩
    refine Finset.mem_map.mpr ⟨f, (mem_rowVariables _ _ _).mpr ?_, rfl⟩
    exact Subtype.ext ((mem_rowVariables _ _ _).mp he)

theorem pigeon_kept (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (u : {u // u ∉ I}) :
    P2MRelativePCRestriction.transport (restriction G I K χ) (clausePolyF (rowClause G u.val)) =
      ML (clausePolyF (rowClause (graph G I K) u)) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  change eval x (P2MRelativePCRestriction.transport (restriction G I K χ)
    (clausePolyF (rowClause G u.val))) = _
  rw [P2MRelativePCRestriction.evaluation, eval_ml, raw_row_variables, raw_row_variables, map_prod, map_prod]
  simp only [CharTwo.sub_eq_add, map_add, map_one, eval_X]
  have hfilter : (∏ e ∈ rowVariables G u.val,
      (1+eval x (P2MRelativePCRestriction.leaf (restriction G I K χ) e))) =
      ∏ e ∈ (rowVariables G u.val).filter (fun e => e.val.2 ∉ K),
        (1+eval x (P2MRelativePCRestriction.leaf (restriction G I K χ) e)) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro e he
    by_cases hv : e.val.2 ∈ K
    · have hu : e.val.1 ∉ I := by rw [(mem_rowVariables _ _ _).mp he]; exact u.property
      simp [P2MRelativePCRestriction.leaf, restriction, hu, hv]
    · simp [hv]
  rw [hfilter, ← row_image G I K u, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e he
  simp only [P2MRelativePCRestriction.leaf, kept, Sum.elim_inl, eval_X]

theorem pigeon_assigned (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (hχedge : ∀ u, G.Adj u.val (χ u)) (u : I) :
    P2MRelativePCRestriction.transport (restriction G I K χ) (clausePolyF (rowClause G u.val)) = 0 := by
  apply multilinear_ext (ml_multilinear _) (by simp [IsMultilinear])
  intro x
  change eval x (P2MRelativePCRestriction.transport (restriction G I K χ)
    (clausePolyF (rowClause G u.val))) = _
  rw [P2MRelativePCRestriction.evaluation, raw_row_variables, map_prod]
  let e : Edge G := ⟨(u.val, χ u), hχedge u⟩
  apply Finset.prod_eq_zero ((mem_rowVariables _ _ _).mpr (show e.val.1 = u.val from rfl))
  simp [e, P2MRelativePCRestriction.leaf, restriction, u.property]

theorem chosen_conflict (G : PCNonBool.BipGraph L R) (I : Finset L) (χ : I → R)
    (hχ : Function.Injective χ) (u w : I) (e f : Edge G)
    (heu : e.val.1 = u.val) (hfv : f.val.1 = w.val)
    (heχ : e.val.2 = χ u) (hfχ : f.val.2 = χ w) (hconflict : Conflict e f) : False := by
  have huw : u = w := by
    rcases hconflict.2 with hrow | hhole
    · exact Subtype.ext (heu.symm.trans (hrow.trans hfv))
    · exact hχ (heχ.symm.trans (hhole.trans hfχ))
  exact hconflict.1 (Subtype.ext (Prod.ext (by rw [heu, hfv, huw]) (by rw [heχ, hfχ, huw])))

theorem chosen_conflict_zero (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (hχ : Function.Injective χ) (hχK : ∀ u, χ u ∈ K) (u : I) (e f : Edge G)
    (heu : e.val.1 = u.val) (heχ : e.val.2 = χ u) (hconflict : Conflict e f) :
    restriction G I K χ f = .inr 0 := by
  by_cases hf : f.val.1 ∈ I
  · have hnot : f.val.2 ≠ χ ⟨f.val.1, hf⟩ := by
      intro hh
      exact chosen_conflict G I χ hχ u ⟨f.val.1, hf⟩ e f heu rfl heχ hh hconflict
    simp only [restriction, dif_pos hf, if_neg hnot]
  · have hfK : f.val.2 ∈ K := by
      rcases hconflict.2 with hrow | hhole
      · exact (hf (hrow ▸ (heu.symm ▸ u.property))).elim
      · rw [← hhole, heχ]
        exact hχK u
    simp only [restriction, dif_neg hf, dif_pos hfK]

theorem inr_one_chosen (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (e : Edge G) (he : restriction G I K χ e = .inr 1) :
    ∃ u : I, e.val.1 = u.val ∧ e.val.2 = χ u := by
  by_cases hu : e.val.1 ∈ I
  · by_cases hv : e.val.2 = χ ⟨e.val.1, hu⟩
    · exact ⟨⟨e.val.1, hu⟩, rfl, hv⟩
    · simp [restriction, hu, hv] at he
  · by_cases hv : e.val.2 ∈ K <;> simp [restriction, hu, hv] at he

theorem inl_conflict (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (e f : Edge G) (e' f' : Edge (graph G I K))
    (he : restriction G I K χ e = .inl e') (hf : restriction G I K χ f = .inl f')
    (hconflict : Conflict e f) : Conflict e' f' := by
  have heq := inl_embedding G I K χ e e' he
  have hfq := inl_embedding G I K χ f f' hf
  refine ⟨fun hh => hconflict.1 (heq.symm.trans ((congrArg (edgeEmbedding G I K) hh).trans hfq)), ?_⟩
  rw [← heq, ← hfq] at hconflict
  rcases hconflict.2 with hrow | hhole
  · exact Or.inl (Subtype.ext hrow)
  · exact Or.inr (Subtype.ext hhole)

theorem quadratic (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (hχ : Function.Injective χ) (hχK : ∀ u, χ u ∈ K)
    (e f : Edge G) (hconflict : Conflict e f) :
    P2MRelativePCRestriction.transport (restriction G I K χ) (X e*X f) = 0 ∨
      ∃ q ∈ fphpG (graph G I K), P2MRelativePCRestriction.transport (restriction G I K χ) (X e*X f) = ML q := by
  have heval : P2MRelativePCRestriction.transport (restriction G I K χ) (X e*X f) =
      ML (P2MRelativePCRestriction.leaf (restriction G I K χ) e*P2MRelativePCRestriction.leaf (restriction G I K χ) f) := by
    change ML (bind₁ _ _) = _
    rw [map_mul, bind₁_X_right, bind₁_X_right]
  rw [heval]
  cases he : restriction G I K χ e with
  | inl e' =>
    cases hf : restriction G I K χ f with
    | inl f' =>
      right
      exact ⟨X e'*X f', conflict_axiom _ _ _ (inl_conflict G I K χ e f e' f' he hf hconflict),
        by simp only [P2MRelativePCRestriction.leaf, he, hf, Sum.elim_inl]⟩
    | inr c =>
      left
      fin_cases c
      · change restriction G I K χ f = .inr 0 at hf
        simp only [P2MRelativePCRestriction.leaf, hf, Sum.elim_inr, C_0, mul_zero, map_zero]
      · obtain ⟨u, hfu, hfχ⟩ := inr_one_chosen G I K χ f hf
        have hsymm : Conflict f e := ⟨hconflict.1.symm, hconflict.2.imp Eq.symm Eq.symm⟩
        have he0 := chosen_conflict_zero G I K χ hχ hχK u f e hfu hfχ hsymm
        simp [P2MRelativePCRestriction.leaf, he0]
  | inr c =>
    left
    fin_cases c
    · change restriction G I K χ e = .inr 0 at he
      simp only [P2MRelativePCRestriction.leaf, he, Sum.elim_inr, C_0, zero_mul, map_zero]
    · obtain ⟨u, heu, heχ⟩ := inr_one_chosen G I K χ e he
      have hf0 := chosen_conflict_zero G I K χ hχ hχK u e f heu heχ hconflict
      simp [P2MRelativePCRestriction.leaf, hf0]

theorem axiom_cases (G : PCNonBool.BipGraph L R) (p : MvPolynomial (Edge G) (ZMod 2))
    (hp : p ∈ fphpG G) :
    (∃ u, p = clausePolyF (F:=ZMod 2) (rowClause G u)) ∨
      ∃ e f : Edge G, Conflict e f ∧ p = X e*X f := by
  rcases hp with ⟨u, rfl⟩ | ⟨u, v, v', h, h', hne, rfl⟩ | ⟨u, u', v, h, h', hne, rfl⟩
  · left
    refine ⟨u, ?_⟩
    rw [raw_row]
    simp only [CharTwo.sub_eq_add]
  · right
    refine ⟨⟨(u, v), h⟩, ⟨(u, v'), h'⟩, ⟨?_, Or.inl rfl⟩, rfl⟩
    intro hh
    exact hne (congrArg (fun e : Edge G => e.val.2) hh)
  · right
    refine ⟨⟨(u, v), h⟩, ⟨(u', v), h'⟩, ⟨?_, Or.inr rfl⟩, rfl⟩
    intro hh
    exact hne (congrArg (fun e : Edge G => e.val.1) hh)

theorem image_axioms (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (hχ : Function.Injective χ) (hχK : ∀ u, χ u ∈ K) (hχedge : ∀ u, G.Adj u.val (χ u))
    (p : MvPolynomial (Edge G) (ZMod 2)) (hp : p ∈ fphpG G) :
    P2MRelativePCRestriction.transport (restriction G I K χ) p = 0 ∨
      ∃ q ∈ fphpG (graph G I K), P2MRelativePCRestriction.transport (restriction G I K χ) p = ML q := by
  rcases axiom_cases G p hp with ⟨u, rfl⟩ | ⟨e, f, hconflict, rfl⟩
  · by_cases hu : u ∈ I
    · exact Or.inl (pigeon_assigned G I K χ hχedge ⟨u, hu⟩)
    · exact Or.inr ⟨clausePolyF (rowClause (graph G I K) ⟨u, hu⟩),
        pigeon_axiom _ _, pigeon_kept G I K χ ⟨u, hu⟩⟩
  · exact quadratic G I K χ hχ hχK e f hconflict

theorem derivation (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (hχ : Function.Injective χ) (hχK : ∀ u, χ u ∈ K) (hχedge : ∀ u, G.Adj u.val (χ u))
    (d B : ℕ) (hdegree : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ d) (hB : max 2 d ≤ B)
    (π : List (MvPolynomial (Edge G) (ZMod 2))) (hπ : PCNonBool.IsDerivation ML (fphpG G) π)
    (hπdegree : ∀ p ∈ π, p.totalDegree ≤ B) :
    ∀ p ∈ π, P2MRelativePCFinite.Derivable (fphpG (graph G I K)) (Ble (Edge (graph G I K)) B)
      (P2MRelativePCRestriction.transport (restriction G I K χ) p) := by
  apply P2MRelativePCRestriction.derivation _ _ _ B _ π hπ hπdegree
  intro p hp
  rcases image_axioms G I K χ hχ hχK hχedge p hp with hz | ⟨q, hq, he⟩
  · rw [hz]
    exact P2MRelativePCFinite.pc_zero _ _
  · rw [he]
    apply P2MRelativePCFinite.pc_axiom _ _ q hq
    exact (P2MBooleanDegreeSpaces.mem_Ble_iff B _).mpr ⟨ml_multilinear _,
      ((P2MBooleanFlip.ml_totalDegree_le _).trans (all_degree _ d
        (P2MProofComplexity.P2MBipartiteDeletionExpansion.left_degree G I K d hdegree) q hq)).trans hB⟩

theorem derivable (G : PCNonBool.BipGraph L R) (I : Finset L) (K : Finset R) (χ : I → R)
    (hχ : Function.Injective χ) (hχK : ∀ u, χ u ∈ K) (hχedge : ∀ u, G.Adj u.val (χ u))
    (d B : ℕ) (hdegree : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ d) (hB : max 2 d ≤ B)
    (p : MvPolynomial (Edge G) (ZMod 2))
    (hp : P2MRelativePCFinite.Derivable (fphpG G) (Ble (Edge G) B) p) :
    P2MRelativePCFinite.Derivable (fphpG (graph G I K)) (Ble (Edge (graph G I K)) B)
      (P2MRelativePCRestriction.transport (restriction G I K χ) p) := by
  rcases hp with rfl | ⟨π, hπ, hmem, hp⟩
  · rw [map_zero]
    exact P2MRelativePCFinite.pc_zero _ _
  · exact derivation G I K χ hχ hχK hχedge d B hdegree hB π hπ
      (fun q hq => ((P2MBooleanDegreeSpaces.mem_Ble_iff B q).mp (hmem q hq)).2) p hp

end SemAC02.Supplement.P2MFPHPPartialMatchingRestriction
end

section
-- Inlined Solutions.P2MFunctionalPHPCompatibleRestriction

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPCompatibleRestriction

open MvPolynomial AC02Frege P2MFunctionalPHPMatchingVariables P2MFunctionalPHPCompatibleSets
open P2MProofComplexity

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

attribute [local instance] Classical.propDecidable

noncomputable def owner (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (u : rows G μ A) : A :=
  ⟨Classical.choose (Finset.mem_image.mp u.property),
    (Classical.choose_spec (Finset.mem_image.mp u.property)).1⟩

theorem owner_row (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (u : rows G μ A) : row G μ (owner G μ A u).val = u.val :=
  (Classical.choose_spec (Finset.mem_image.mp u.property)).2

theorem owner_eq (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (hA : Compatible G μ A) (e : A) (u : rows G μ A) (hu : u.val = row G μ e.val) :
    owner G μ A u = e := by
  apply Subtype.ext
  exact row_injective G μ A hA (owner G μ A u).property e.property ((owner_row G μ A u).trans hu)

noncomputable def choice (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (β : A → Bool) (u : rows G μ A) : R :=
  if β (owner G μ A u) then hole G μ (owner G μ A u).val else reserved G μ (owner G μ A u).val

theorem choice_pair (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (β : A → Bool) (u : rows G μ A) : choice G μ A β u ∈
      ({reserved G μ (owner G μ A u).val, hole G μ (owner G μ A u).val} : Finset R) := by
  unfold choice
  split_ifs <;> simp

theorem choice_injective (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (hA : Compatible G μ A) (β : A → Bool) : Function.Injective (choice G μ A β) := by
  intro u w he
  have how : owner G μ A u = owner G μ A w := by
    by_contra hne
    have hne' : (owner G μ A u).val ≠ (owner G μ A w).val := by
      exact fun hh => hne (Subtype.ext hh)
    have hd := P2MCompatibleEdgeDeletion.pairwise_holes (addMatching G μ) (row G μ)
      (reserved G μ) (hole G μ) (matched G μ) (edge G μ) A hA
      (owner G μ A u).property (owner G μ A w).property hne'
    exact Finset.disjoint_left.mp hd (choice_pair G μ A β u) (he ▸ choice_pair G μ A β w)
  apply Subtype.ext
  exact (owner_row G μ A u).symm.trans ((congrArg (fun e : A => row G μ e.val) how).trans (owner_row G μ A w))

theorem choice_mem (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (β : A → Bool) (u : rows G μ A) : choice G μ A β u ∈ holes G μ A :=
  Finset.mem_biUnion.mpr ⟨(owner G μ A u).val, (owner G μ A u).property, choice_pair G μ A β u⟩

theorem choice_edge (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (β : A → Bool) (u : rows G μ A) : (addMatching G μ).Adj u.val (choice G μ A β u) := by
  rw [← owner_row G μ A u]
  unfold choice
  split_ifs
  · exact edge G μ _
  · exact matched G μ _

noncomputable def restriction (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (β : A → Bool) : Edge (addMatching G μ) →
      Edge (P2MBipartiteInducedSubgraph.graph (addMatching G μ) (rows G μ A) (holes G μ A)) ⊕ ZMod 2 :=
  P2MFPHPPartialMatchingRestriction.restriction (addMatching G μ) (rows G μ A) (holes G μ A) (choice G μ A β)

theorem selected (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (hA : Compatible G μ A) (β : A → Bool) (e : A) :
    restriction G μ A β e.val.val = .inr (if β e then 1 else 0) := by
  have hu : e.val.val.val.1 ∈ rows G μ A := Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩
  have ho : owner G μ A ⟨e.val.val.val.1, hu⟩ = e := owner_eq G μ A hA e _ rfl
  unfold restriction P2MFPHPPartialMatchingRestriction.restriction
  rw [dif_pos hu]
  simp only [choice, ho]
  have hn : e.val.val.val.2 ≠ reserved G μ e.val := (reserved_ne G μ e.val).symm
  cases hb : β e <;> simp [hb, hole, hn]

theorem free_outside_zero (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (hA : Compatible G μ A) (β : A → Bool) (e : Free G μ)
    (houtside : e ∉ A.map (freeEmbedding G μ)) (hrow : e.val.val.1 ∈ rows G μ A) :
    restriction G μ A β e.val = .inr 0 := by
  let u : rows G μ A := ⟨e.val.val.1, hrow⟩
  let a := owner G μ A u
  have harow : row G μ a.val = e.val.val.1 := owner_row G μ A u
  have hnres : e.val.val.2 ≠ reserved G μ a.val := by
    intro hh
    apply e.property
    rw [hh, reserved_spec G μ a.val]
    exact harow.symm
  have hnhole : e.val.val.2 ≠ hole G μ a.val := by
    intro hh
    have heq : freeEmbedding G μ a.val = e := by
      apply Subtype.ext
      exact Subtype.ext (Prod.ext harow hh.symm)
    exact houtside (Finset.mem_map.mpr ⟨a.val, a.property, heq⟩)
  have hnchoice : e.val.val.2 ≠ choice G μ A β u := by
    unfold choice
    split_ifs
    · exact hnhole
    · exact hnres
  unfold restriction P2MFPHPPartialMatchingRestriction.restriction
  rw [dif_pos hrow, if_neg hnchoice]

theorem free_outside_independent (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (hA : Compatible G μ A) (e : Free G μ) (houtside : e ∉ A.map (freeEmbedding G μ))
    (β γ : A → Bool) : restriction G μ A β e.val = restriction G μ A γ e.val := by
  by_cases hrow : e.val.val.1 ∈ rows G μ A
  · rw [free_outside_zero G μ A hA β e houtside hrow, free_outside_zero G μ A hA γ e houtside hrow]
  · unfold restriction P2MFPHPPartialMatchingRestriction.restriction
    simp only [dif_neg hrow]

end SemAC02.Supplement.P2MFunctionalPHPCompatibleRestriction
end

section
-- Inlined Solutions.P2MBooleanCubeCancellation

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MBooleanCubeCancellation

variable {I A : Type} [Fintype I] [DecidableEq I] [CommRing A] [CharP A 2]

def toggle (i : I) (β : I → Bool) : I → Bool := Function.update β i (!(β i))

theorem toggle_involutive (i : I) (β : I → Bool) : toggle i (toggle i β) = β := by
  funext j
  by_cases h : j = i <;> simp [toggle, Function.update_apply, h]

theorem toggle_ne (i : I) (β : I → Bool) : toggle i β ≠ β := by
  intro h
  have hh := congrFun h i
  simp only [toggle, Function.update_self] at hh
  cases hβ : β i <;> simp_all

theorem sum_eq_zero (i : I) (f : (I → Bool) → A)
    (hf : ∀ β, f (toggle i β) = f β) : ∑ β, f β = 0 := by
  apply Finset.sum_ninvolution (toggle i)
  · intro β
    rw [hf β]
    exact CharTwo.add_self_eq_zero _
  · intro β _
    exact toggle_ne i β
  · intro β
    exact Finset.mem_univ _
  · exact toggle_involutive i

theorem sum_full_product : (∑ β : I → Bool, ∏ i, (if β i then (1 : A) else 0)) = 1 := by
  classical
  have hprod (β : I → Bool) : (∏ i, (if β i then (1 : A) else 0)) =
      if β = (fun _ => true) then 1 else 0 := by
    by_cases he : β = fun _ => true
    · simp [he]
    · rw [if_neg he]
      obtain ⟨i, hi⟩ : ∃ i, β i = false := by
        by_contra h
        push_neg at h
        apply he
        funext i
        cases hβ : β i <;> simp_all
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  simp only [hprod]
  simp

end P2MProofComplexity.P2MBooleanCubeCancellation
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
-- Inlined Solutions.P2MAffineBooleanForms

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MAffineBooleanForms

open ACirc P2MArithmeticCircuitBasics MvPolynomial

lemma zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

noncomputable def evalMap {V : Type} [Fintype V] (x : V → Bool) :
    (Option V → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := v none+∑ i, v (some i)*(if x i then 1 else 0)
  map_add' v w := by simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]; ring
  map_smul' a v := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_add,Finset.mul_sum,mul_assoc] <;> ring

def equationVector {V : Type} (e : LinEq V) : Option V → ZMod 2
  | none => e.2+1
  | some i => e.1 i

lemma vector_nonzero_iff {V : Type} [Fintype V] (e : LinEq V) (x : V → Bool) :
    evalMap x (equationVector e) ≠ 0 ↔ e.Sat x := by
  change e.2+1+(∑ i, e.1 i*(if x i then 1 else 0)) ≠ 0 ↔
    (∑ i, e.1 i*(if x i then 1 else 0)) = e.2
  let l := ∑ i, e.1 i*(if x i then (1 : ZMod 2) else 0)
  change e.2+1+l ≠ 0 ↔ l = e.2
  rw [show e.2+1+l = 1+(l+e.2) by ring,← CharTwo.add_eq_zero]
  rcases zero_or_one (l+e.2) with h | h
  · norm_num [h]
  · simp only [h,CharTwo.add_self_eq_zero,ne_eq,not_true_eq_false,one_ne_zero]

noncomputable def affineCircuit {V : Type} [Fintype V] (v : Option V → ZMod 2) : ACirc (ZMod 2) V :=
  .sum ((v none+1,.const 1)::(Finset.univ.toList.map (fun i => (v (some i),.var i))))

lemma cval_affine {V : Type} [Fintype V] (v : Option V → ZMod 2) (x : V → Bool) :
    cval (affineCircuit v) x = 1+evalMap x v := by
  rw [affineCircuit,cval_sum]
  simp only [List.map_cons,List.sum_cons,List.map_map,Function.comp_def,cval,polyFn,toPoly,
    eval_C,eval_X,mul_one]
  rw [Finset.sum_map_toList]
  change v none+1+(∑ i, v (some i)*(if x i then 1 else 0)) =
    1+(v none+∑ i, v (some i)*(if x i then 1 else 0))
  ring

lemma affine_layer {V : Type} [Fintype V] (v : Option V → ZMod 2) :
    IsSumOf IsLeaf (affineCircuit v) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · trivial
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    trivial

lemma subterms_affine {V : Type} [Fintype V] (v : Option V → ZMod 2) (c : ACirc (ZMod 2) V)
    (hc : c ∈ subterms (affineCircuit v)) :
    c = affineCircuit v ∨ c = .const 1 ∨ ∃ i : V, c = .var i := by
  classical
  rcases (mem_subterms_sum c _).mp hc with he | ⟨q,hq,hc⟩
  · exact Or.inl he
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inl (by simpa only [subterms,Finset.mem_singleton] using hc))
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      exact Or.inr (Or.inr ⟨i,by simpa only [subterms,Finset.mem_singleton] using hc⟩)

end SemAC02.Supplement.P2MAffineBooleanForms
end

section
-- Inlined Solutions.P2MBooleanMonomialExtraction

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MBooleanMonomialExtraction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

variable {V A : Type} [DecidableEq V] [CommRing A] [CharP A 2]

theorem monomial (S T : Finset V) (hcard : T.card ≤ S.card)
    (g : (S → Bool) → V → A)
    (hselected : ∀ β (v : S), g β v.val = if β v then 1 else 0)
    (houtside : ∀ v, v ∉ S → ∀ β γ, g β v = g γ v) :
    (∑ β : S → Bool, ∏ v ∈ T, g β v) = if T = S then 1 else 0 := by
  classical
  by_cases he : T = S
  · subst T
    rw [if_pos rfl]
    have hprod (β : S → Bool) : (∏ v ∈ S, g β v) = ∏ v : S, (if β v then (1 : A) else 0) := by
      rw [← Finset.prod_attach]
      simp only [Finset.attach_eq_univ]
      exact Finset.prod_congr rfl (fun v _ => hselected β v)
    simp only [hprod]
    exact P2MBooleanCubeCancellation.sum_full_product
  · rw [if_neg he]
    have hnot : ¬ S ⊆ T := by
      intro hsub
      exact he (Finset.eq_of_subset_of_card_le hsub hcard).symm
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hnot
    apply P2MBooleanCubeCancellation.sum_eq_zero (⟨i, hiS⟩ : S)
    intro β
    apply Finset.prod_congr rfl
    intro v hv
    by_cases hvS : v ∈ S
    · rw [hselected _ ⟨v, hvS⟩, hselected _ ⟨v, hvS⟩]
      have hne : (⟨v, hvS⟩ : S) ≠ ⟨i, hiS⟩ := by
        intro hh
        have hvI := congrArg Subtype.val hh
        change v = i at hvI
        exact hiT (by rwa [← hvI])
      simp only [P2MBooleanCubeCancellation.toggle, Function.update_of_ne hne]
    · exact houtside v hvS _ _

/-- Summing all assignments to a monomial of maximum degree extracts its
coefficient; variables outside that monomial may be restricted arbitrarily,
provided those restrictions do not depend on the selected assignment. -/
theorem polynomial {W : Type} (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (d : V →₀ ℕ) (hd : d ∈ p.support)
    (hmax : ∀ e ∈ p.support, e.support.card ≤ d.support.card)
    (g : (d.support → Bool) → V → MvPolynomial W (ZMod 2))
    (hselected : ∀ β (v : d.support), g β v.val = if β v then 1 else 0)
    (houtside : ∀ v, v ∉ d.support → ∀ β γ, g β v = g γ v) :
    (∑ β : d.support → Bool, bind₁ (g β) p) = 1 := by
  classical
  have hcoeff : p.coeff d = 1 := by
    have hnonzero := mem_support_iff.mp hd
    rcases SemAC02.Supplement.P2MAffineBooleanForms.zero_or_one (p.coeff d) with hz | ho
    · exact (hnonzero hz).elim
    · exact ho
  have hexpand (β : d.support → Bool) : bind₁ (g β) p =
      ∑ e ∈ p.support, p.coeff e • ∏ v ∈ e.support, g β v := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [P2MBooleanBasis.squarefree_monomial e _ (hp e he), map_smul]
    simp only [xMon, map_prod, bind₁_X_right]
  simp only [hexpand]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum]
  have hmon (e : V →₀ ℕ) (he : e ∈ p.support) :
      (∑ β : d.support → Bool, ∏ v ∈ e.support, g β v) = if e = d then 1 else 0 := by
    rw [monomial d.support e.support (hmax e he) g hselected houtside]
    have heq : e.support = d.support ↔ e = d := by
      constructor
      · exact P2MBooleanRestrictions.multilinear_exponent_ext e d (hp e he) (hp d hd)
      · exact fun h => congrArg Finsupp.support h
    simp only [heq]
  rw [Finset.sum_eq_single d]
  · rw [hmon d hd, if_pos rfl, hcoeff, one_smul]
  · intro e he hne
    rw [hmon e he, if_neg hne, smul_zero]
  · intro hnot
    exact (hnot hd).elim

end P2MProofComplexity.P2MBooleanMonomialExtraction
end

section
-- Inlined Solutions.P2MBooleanRestrictionExtraction

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MBooleanRestrictionExtraction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

variable {U V W : Type} [Finite U] [Finite V] [Finite W] [DecidableEq V]

theorem renamed (f : U → V) (ρ : V → W ⊕ ZMod 2) (p : MvPolynomial U (ZMod 2)) :
    P2MRelativePCRestriction.transport ρ (P2MRelativePCRenaming.transport f p) =
      P2MRelativePCRestriction.transport (ρ ∘ f) p := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  change eval x (P2MRelativePCRestriction.transport ρ (P2MRelativePCRenaming.transport f p)) =
    eval x (P2MRelativePCRestriction.transport (ρ ∘ f) p)
  rw [P2MRelativePCRestriction.evaluation, P2MRelativePCRestriction.evaluation]
  change eval (fun v => eval x (P2MRelativePCRestriction.leaf ρ v)) (ML (rename f p)) = _
  rw [eval_ml, eval_rename]
  rfl

theorem sum_eq_one (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (d : V →₀ ℕ) (hd : d ∈ p.support)
    (hmax : ∀ e ∈ p.support, e.support.card ≤ d.support.card)
    (ρ : (d.support → Bool) → V → W ⊕ ZMod 2)
    (hselected : ∀ β (v : d.support), P2MRelativePCRestriction.leaf (ρ β) v.val = if β v then 1 else 0)
    (houtside : ∀ v, v ∉ d.support → ∀ β γ,
      P2MRelativePCRestriction.leaf (ρ β) v = P2MRelativePCRestriction.leaf (ρ γ) v) :
    (∑ β : d.support → Bool, P2MRelativePCRestriction.transport (ρ β) p) = 1 := by
  have hraw := P2MProofComplexity.P2MBooleanMonomialExtraction.polynomial p hp d hd hmax
    (fun β => P2MRelativePCRestriction.leaf (ρ β)) hselected houtside
  change (∑ β : d.support → Bool, ML (bind₁ (P2MRelativePCRestriction.leaf (ρ β)) p)) = 1
  rw [← map_sum, hraw]
  exact ml_of_multilinear _ (by simp [IsMultilinear])

end SemAC02.Supplement.P2MBooleanRestrictionExtraction
end

section
-- Inlined Solutions.P2MFunctionalPHPRestrictionExtraction

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPRestrictionExtraction

open MvPolynomial AC02Frege P2MFunctionalPHPMatchingVariables P2MFunctionalPHPCompatibleSets
open P2MFunctionalPHPCompatibleRestriction

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

noncomputable def supportLabel (G : PCNonBool.BipGraph L R) (μ : R → L) (A : Finset (Selected G μ))
    (S : Finset (Free G μ)) (himage : A.map (freeEmbedding G μ) = S) (a : A) : S :=
  ⟨freeEmbedding G μ a.val, by rw [← himage]; exact Finset.mem_map.mpr ⟨a.val, a.property, rfl⟩⟩

theorem extraction (G : PCNonBool.BipGraph L R) (μ : R → L)
    (p : MvPolynomial (Free G μ) (ZMod 2)) (hp : IsMultilinear p)
    (d : Free G μ →₀ ℕ) (hd : d ∈ p.support)
    (hmax : ∀ e ∈ p.support, e.support.card ≤ d.support.card)
    (A : Finset (Selected G μ)) (hA : Compatible G μ A)
    (himage : A.map (freeEmbedding G μ) = d.support) :
    (∑ β : d.support → Bool, P2MRelativePCRestriction.transport
      (restriction G μ A (β ∘ supportLabel G μ A d.support himage))
      (P2MRelativePCRenaming.transport Subtype.val p)) = 1 := by
  classical
  let label := supportLabel G μ A d.support himage
  let ρ (β : d.support → Bool) (e : Free G μ) := restriction G μ A (β ∘ label) e.val
  have hselected : ∀ β (v : d.support), P2MRelativePCRestriction.leaf (ρ β) v.val = if β v then 1 else 0 := by
    intro β v
    have hvA : v.val ∈ A.map (freeEmbedding G μ) := by rw [himage]; exact v.property
    obtain ⟨e, he, heq⟩ := Finset.mem_map.mp hvA
    let a : A := ⟨e, he⟩
    have hlabel : label a = v := Subtype.ext heq
    have hedge : e.val = v.val.val := congrArg (fun e : Free G μ => e.val) heq
    change Sum.elim X C (restriction G μ A (β ∘ label) v.val.val) = _
    rw [← hedge, selected G μ A hA (β ∘ label) a]
    simp only [Function.comp_apply, hlabel]
    cases hb : β v <;> simp [hb]
  have houtside : ∀ v, v ∉ d.support → ∀ β γ,
      P2MRelativePCRestriction.leaf (ρ β) v = P2MRelativePCRestriction.leaf (ρ γ) v := by
    intro v hv β γ
    have hvA : v ∉ A.map (freeEmbedding G μ) := by rwa [himage]
    exact congrArg (Sum.elim X C)
      (free_outside_independent G μ A hA v hvA (β ∘ label) (γ ∘ label))
  have hsum := P2MBooleanRestrictionExtraction.sum_eq_one p hp d hd hmax ρ hselected houtside
  simp_rw [P2MBooleanRestrictionExtraction.renamed]
  exact hsum

end SemAC02.Supplement.P2MFunctionalPHPRestrictionExtraction
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
-- Inlined Solutions.P2MSPSAffineSubstitution

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MSPSAffineSubstitution

open ACirc P2MArithmeticCircuitBasics

variable {F V U : Type} [Field F]

def leafTerms (A : V → List (F × ACirc F U)) : ACirc F V → List (F × ACirc F U)
  | .var v => A v
  | .const a => [(a, .const 1)]
  | _ => []

def bottom (A : V → List (F × ACirc F U)) : ACirc F V → ACirc F U
  | .sum ps => .sum (ps.flatMap (fun p => (leafTerms A p.2).map (fun q => (p.1*q.1, q.2))))
  | _ => .sum []

def term (A : V → List (F × ACirc F U)) : ACirc F V → ACirc F U
  | .prod cs => .prod (cs.map (bottom A))
  | _ => .prod []

def line (A : V → List (F × ACirc F U)) : ACirc F V → ACirc F U
  | .sum ps => .sum (ps.map (fun p => (p.1, term A p.2)))
  | _ => .sum []

theorem leaf_terms_layer (A : V → List (F × ACirc F U))
    (hA : ∀ v, ∀ p ∈ A v, IsLeaf p.2) (c : ACirc F V) :
    ∀ p ∈ leafTerms A c, IsLeaf p.2 := by
  cases c <;> simp only [leafTerms, List.mem_singleton, List.not_mem_nil, false_implies, implies_true]
  · exact hA _
  · intro p hp
    subst p
    trivial

theorem bottom_layer (A : V → List (F × ACirc F U))
    (hA : ∀ v, ∀ p ∈ A v, IsLeaf p.2) (c : ACirc F V) : IsSumOf IsLeaf (bottom A c) := by
  cases c <;> try exact fun p hp => (List.not_mem_nil hp).elim
  case sum ps =>
    intro p hp
    obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    exact leaf_terms_layer A hA q.2 r hr

theorem term_layer (A : V → List (F × ACirc F U))
    (hA : ∀ v, ∀ p ∈ A v, IsLeaf p.2) (c : ACirc F V) :
    IsProdOf (IsSumOf IsLeaf) (term A c) := by
  cases c <;> try exact fun d hd => (List.not_mem_nil hd).elim
  case prod cs =>
    intro d hd
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
    exact bottom_layer A hA b

theorem line_layer (A : V → List (F × ACirc F U))
    (hA : ∀ v, ∀ p ∈ A v, IsLeaf p.2) (c : ACirc F V) : IsSPS (line A c) := by
  cases c <;> try exact fun p hp => (List.not_mem_nil hp).elim
  case sum ps =>
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact term_layer A hA q.2

theorem leaf_terms_value (A : V → List (F × ACirc F U))
    (η : (U → Bool) → V → Bool)
    (hA : ∀ v y, ((A v).map (fun p => p.1*cval p.2 y)).sum = boolPt (η y) v)
    (c : ACirc F V) (hc : IsLeaf c) (y : U → Bool) :
    ((leafTerms A c).map (fun p => p.1*cval p.2 y)).sum = cval c (η y) := by
  cases c with
  | var v => simpa only [leafTerms, cval, polyFn, toPoly, MvPolynomial.eval_X] using hA v y
  | const a => simp [leafTerms, cval, polyFn, toPoly]
  | sum ps => exact hc.elim
  | prod cs => exact hc.elim

theorem weighted_value (a : F) (qs : List (F × ACirc F U)) (y : U → Bool) :
    ((qs.map (fun q => (a*q.1, q.2))).map (fun q => q.1*cval q.2 y)).sum =
      a*(qs.map (fun q => q.1*cval q.2 y)).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih => simp only [List.map_cons, List.sum_cons, mul_add, mul_assoc, ih]

theorem bottom_value (A : V → List (F × ACirc F U))
    (η : (U → Bool) → V → Bool)
    (hA : ∀ v y, ((A v).map (fun p => p.1*cval p.2 y)).sum = boolPt (η y) v)
    (c : ACirc F V) (hc : IsSumOf IsLeaf c) (y : U → Bool) :
    cval (bottom A c) y = cval c (η y) := by
  cases c with
  | var v => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    rw [bottom, cval_sum, cval_sum]
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      rw [weighted_value, leaf_terms_value A η hA p.2 (hc p (by simp)) y]
      congr 1
      exact ih (fun q hq => hc q (List.mem_cons_of_mem p hq))

theorem term_value (A : V → List (F × ACirc F U))
    (η : (U → Bool) → V → Bool)
    (hA : ∀ v y, ((A v).map (fun p => p.1*cval p.2 y)).sum = boolPt (η y) v)
    (c : ACirc F V) (hc : IsProdOf (IsSumOf IsLeaf) c) (y : U → Bool) :
    cval (term A c) y = cval c (η y) := by
  cases c with
  | var v => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs =>
    simp only [term, cval_prod, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun b hb => bottom_value A η hA b (hc b hb) y)

theorem line_value (A : V → List (F × ACirc F U))
    (η : (U → Bool) → V → Bool)
    (hA : ∀ v y, ((A v).map (fun p => p.1*cval p.2 y)).sum = boolPt (η y) v)
    (c : ACirc F V) (hc : IsSPS c) (y : U → Bool) :
    cval (line A c) y = cval c (η y) := by
  cases c with
  | var v => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    simp only [line, cval_sum, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro p hp
    rw [term_value A η hA p.2 (hc p hp) y]

theorem top_terms (A : V → List (F × ACirc F U)) (c : ACirc F V) :
    topTerms (line A c) = (topTerms c).map (term A) := by
  cases c <;> simp [line, topTerms, List.map_map, Function.comp_def]

theorem top_bound (A : V → List (F × ACirc F U))
    (η : (U → Bool) → V → Bool)
    (hA : ∀ v y, ((A v).map (fun p => p.1*cval p.2 y)).sum = boolPt (η y) v)
    (π : List (ACirc F V)) (hπ : ∀ c ∈ π, IsSPS c) :
    topS Set.univ (π.map (line A)) ≤ topS Set.univ π := by
  apply P2MProofTopFunctions.projection_bound η (line A) (term A) π (top_terms A)
  intro c hc t ht y
  have hc' := hπ c hc
  cases c with
  | var v => exact hc'.elim
  | const a => exact hc'.elim
  | prod cs => exact hc'.elim
  | sum ps =>
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact term_value A η hA p.2 (hc' p hp) y

theorem refutation (A : V → List (F × ACirc F U))
    (hleaves : ∀ v, ∀ p ∈ A v, IsLeaf p.2)
    (η : (U → Bool) → V → Bool)
    (hA : ∀ v y, ((A v).map (fun p => p.1*cval p.2 y)).sum = boolPt (η y) v)
    (Ax : Set ((V → Bool) → F)) (π : List (ACirc F V))
    (hπ : IsSemPCRef IsSPS Set.univ Ax π) :
    IsSemPCRef IsSPS Set.univ ((fun a => fun y => a (η y)) '' Ax) (π.map (line A)) := by
  have hvalue (c : ACirc F V) (hc : c ∈ π) (y : U → Bool) : cval (line A c) y = cval c (η y) :=
    line_value A η hA c (hπ.1 c hc) y
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact line_layer A hleaves a
  · intro i hi
    have hi' : i < π.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map]
    rcases hπ.2.1 i hi' with ⟨a, ha, he⟩ | he | ⟨j, l, hj, hl, he⟩
    · left
      refine ⟨fun y => a (η y), ⟨a, ha, rfl⟩, ?_⟩
      intro y hy
      rw [hvalue _ (List.getElem_mem hi') y]
      exact he _ (Set.mem_univ _)
    · right; left
      intro y hy
      rw [hvalue _ (List.getElem_mem hi') y]
      exact he _ (Set.mem_univ _)
    · right; right
      refine ⟨j, l, hj, hl, ?_⟩
      intro y hy hp hq
      rw [hvalue _ (List.getElem_mem hi') y]
      apply he (η y) (Set.mem_univ _)
      · rwa [hvalue _ (List.getElem_mem (hj.trans hi')) y] at hp
      · rwa [hvalue _ (List.getElem_mem (hl.trans hi')) y] at hq
  · obtain ⟨c, hc, hval⟩ := hπ.2.2
    refine ⟨line A c, ?_, ?_⟩
    · rw [List.getLast?_map, hc]; rfl
    · intro y hy
      rw [hvalue c (List.mem_of_getLast? hc) y]
      exact hval _ (Set.mem_univ _)

end SemAC02.Supplement.P2MSPSAffineSubstitution
end

section
-- Inlined Solutions.P2MFunctionalPHPAffineSubstitution

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPAffineSubstitution

open MvPolynomial ACirc AC02Frege AC02Frege.P2MBooleanAlgebra P2MArithmeticCircuitBasics P2MFunctionalPHPMatchingVariables

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

noncomputable def row (G : PCNonBool.BipGraph L R) (μ : R → L) (u : L) : Finset (Free G μ) :=
  Finset.univ.filter (fun e => e.val.val.1 = u)

noncomputable def rho (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Edge (addMatching G μ)) :
    MvPolynomial (Free G μ) (ZMod 2) :=
  if h : e.val.1 = μ e.val.2 then 1 + ∑ f ∈ row G μ e.val.1, X f else X ⟨e, h⟩

noncomputable def terms (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Edge (addMatching G μ)) :
    List (ZMod 2 × ACirc (ZMod 2) (Free G μ)) :=
  if h : e.val.1 = μ e.val.2 then
    (1, .const 1) :: ((row G μ e.val.1).toList.map (fun f => (1, .var f)))
  else [(1, .var ⟨e, h⟩)]

theorem leaves (G : PCNonBool.BipGraph L R) (μ : R → L) :
    ∀ e, ∀ p ∈ terms G μ e, IsLeaf p.2 := by
  classical
  intro e p hp
  unfold terms at hp
  split_ifs at hp with h
  · rcases List.mem_cons.mp hp with he | hp
    · subst p; trivial
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
      trivial
  · have he := List.mem_singleton.mp hp
    subst p
    trivial

theorem polynomial (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Edge (addMatching G μ)) :
    (ACirc.sum (terms G μ e)).toPoly = rho G μ e := by
  classical
  by_cases he : e.val.1 = μ e.val.2
  · simp only [terms, dif_pos he, toPoly_sum, List.map_cons, List.sum_cons, toPoly,
      C_1, mul_one, List.map_map, Function.comp_def, one_mul, rho]
    rw [Finset.sum_map_toList]
  · simp [terms, rho, he, toPoly_sum, toPoly]

theorem rho_degree (G : PCNonBool.BipGraph L R) (μ : R → L) (e : Edge (addMatching G μ)) :
    (rho G μ e).totalDegree ≤ 1 := by
  classical
  unfold rho
  split_ifs
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact totalDegree_finsetSum_le (fun f hf => by simp)
  · simp

noncomputable def fieldBool (a : ZMod 2) : Bool := decide (a = 1)

theorem fieldBool_value (a : ZMod 2) : (if fieldBool a then (1 : ZMod 2) else 0) = a := by
  rcases P2MAffineBooleanForms.zero_or_one a with he | he <;> rw [he] <;> norm_num [fieldBool]

noncomputable def liftPoint (G : PCNonBool.BipGraph L R) (μ : R → L)
    (y : Free G μ → Bool) : Edge (addMatching G μ) → Bool :=
  fun e => fieldBool (polyFn (rho G μ e) y)

theorem terms_value (G : PCNonBool.BipGraph L R) (μ : R → L)
    (e : Edge (addMatching G μ)) (y : Free G μ → Bool) :
    ((terms G μ e).map (fun p => p.1*cval p.2 y)).sum = boolPt (liftPoint G μ y) e := by
  have hh : ((terms G μ e).map (fun p => p.1*cval p.2 y)).sum = polyFn (rho G μ e) y := by
    rw [← polynomial G μ e]
    exact (cval_sum (terms G μ e) y).symm
  rw [hh]
  exact (fieldBool_value (polyFn (rho G μ e) y)).symm

noncomputable def sigma (G : PCNonBool.BipGraph L R) (μ : R → L) :
    MvPolynomial (Edge (addMatching G μ)) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Free G μ) (ZMod 2) :=
  ML.comp (aeval (rho G μ)).toLinearMap

theorem degree_le (G : PCNonBool.BipGraph L R) (μ : R → L)
    (p : MvPolynomial (Edge (addMatching G μ)) (ZMod 2)) :
    (sigma G μ p).totalDegree ≤ p.totalDegree := by
  apply (P2MBooleanFlip.ml_totalDegree_le _).trans
  rw [aeval_eq_bind₁]
  exact P2MBooleanFlip.bind_linear_totalDegree_le (rho G μ) (rho_degree G μ) p

theorem evaluation (G : PCNonBool.BipGraph L R) (μ : R → L)
    (p : MvPolynomial (Edge (addMatching G μ)) (ZMod 2)) (y : Free G μ → Bool) :
    polyFn (sigma G μ p) y = polyFn p (liftPoint G μ y) := by
  change eval (boolPt y) (ML (aeval (rho G μ) p)) = eval (boolPt (liftPoint G μ y)) p
  rw [eval_ml, map_aeval]
  have he : (eval (boolPt y)).comp (algebraMap (ZMod 2) (MvPolynomial (Free G μ) (ZMod 2))) =
      RingHom.id (ZMod 2) := by ext a; simp
  rw [he]
  change eval (fun e => eval (boolPt y) (rho G μ e)) p = eval (boolPt (liftPoint G μ y)) p
  have heval : (fun e => eval (boolPt y) (rho G μ e)) = boolPt (liftPoint G μ y) := by
    funext e
    exact (fieldBool_value (polyFn (rho G μ e) y)).symm
  rw [heval]

theorem refutation (G : PCNonBool.BipGraph L R) (μ : R → L)
    (π : List (ACirc (ZMod 2) (Edge (addMatching G μ))))
    (hπ : IsSemPCRef IsSPS Set.univ (polyAx (fphpG (addMatching G μ))) π) :
    IsSemPCRef IsSPS Set.univ (polyAx (sigma G μ '' fphpG (addMatching G μ)))
      (π.map (P2MSPSAffineSubstitution.line (terms G μ))) ∧
    topS Set.univ (π.map (P2MSPSAffineSubstitution.line (terms G μ))) ≤ topS Set.univ π := by
  have hAx : ((fun a => fun y => a (liftPoint G μ y)) '' polyAx (fphpG (addMatching G μ))) =
      polyAx (sigma G μ '' fphpG (addMatching G μ)) := by
    ext a
    constructor
    · rintro ⟨b, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨sigma G μ p, ⟨p, hp, rfl⟩, funext (fun y => evaluation G μ p y)⟩
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨polyFn p, ⟨p, hp, rfl⟩, funext (fun y => (evaluation G μ p y).symm)⟩
  refine ⟨?_, P2MSPSAffineSubstitution.top_bound (terms G μ) (liftPoint G μ) (terms_value G μ) π hπ.1⟩
  rw [← hAx]
  exact P2MSPSAffineSubstitution.refutation (terms G μ) (leaves G μ) (liftPoint G μ) (terms_value G μ) _ π hπ

end SemAC02.Supplement.P2MFunctionalPHPAffineSubstitution
end

section
-- Inlined Solutions.P2MFunctionalPHPFreeRow

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPFreeRow

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MFunctionalPHPMatchingVariables

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem matching_iff (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (e f : Edge (addMatching G μ)) (he : e.val.1 = μ e.val.2) (hf : f.val.1 = e.val.1) :
    f.val.1 = μ f.val.2 ↔ f = e := by
  constructor
  · intro hmatch
    have hhole : f.val.2 = e.val.2 := hμ (hmatch.symm.trans (hf.trans he))
    exact Subtype.ext (Prod.ext hf hhole)
  · intro hfe
    subst f
    exact he

theorem row_image (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (e : Edge (addMatching G μ)) (he : e.val.1 = μ e.val.2) :
    (P2MFunctionalPHPAffineSubstitution.row G μ e.val.1).map
        (Function.Embedding.subtype (fun f : Edge (addMatching G μ) => f.val.1 ≠ μ f.val.2)) =
      (P2MFunctionalPHPCoveredRepresentation.rowVariables (addMatching G μ) e.val.1).erase e := by
  classical
  ext f
  simp only [Finset.mem_map, Finset.mem_erase, P2MFunctionalPHPCoveredRepresentation.mem_rowVariables]
  constructor
  · rintro ⟨f', hf', rfl⟩
    have hrow := (Finset.mem_filter.mp hf').2
    exact ⟨fun hfe => f'.property ((matching_iff G μ hμ e f'.val he hrow).mpr hfe), hrow⟩
  · rintro ⟨hne, hrow⟩
    have hfree : f.val.1 ≠ μ f.val.2 := fun hh => hne ((matching_iff G μ hμ e f he hrow).mp hh)
    exact ⟨⟨f, hfree⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow⟩, rfl⟩

theorem sum_free (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (e : Edge (addMatching G μ)) (he : e.val.1 = μ e.val.2)
    (x : Edge (addMatching G μ) → ZMod 2) :
    (∑ f ∈ P2MFunctionalPHPAffineSubstitution.row G μ e.val.1, x f.val) + x e =
      ∑ f ∈ P2MFunctionalPHPCoveredRepresentation.rowVariables (addMatching G μ) e.val.1, x f := by
  have hsum := congrArg (fun S : Finset (Edge (addMatching G μ)) => ∑ f ∈ S, x f) (row_image G μ hμ e he)
  rw [Finset.sum_map] at hsum
  simp only [Function.Embedding.subtype_apply] at hsum
  rw [hsum]
  apply Finset.sum_erase_add
  exact (P2MFunctionalPHPCoveredRepresentation.mem_rowVariables _ _ _).mpr rfl

theorem rho_value (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (x : Edge (addMatching G μ) → ZMod 2) (e : Edge (addMatching G μ))
    (hrow : 1+(∑ f ∈ P2MFunctionalPHPCoveredRepresentation.rowVariables (addMatching G μ) e.val.1, x f) = 0) :
    eval (fun f : Free G μ => x f.val) (P2MFunctionalPHPAffineSubstitution.rho G μ e) = x e := by
  classical
  unfold P2MFunctionalPHPAffineSubstitution.rho
  split_ifs with he
  · simp only [map_add, map_one, map_sum, eval_X]
    have hsum := sum_free G μ hμ e he x
    have hh : (1+∑ f ∈ P2MFunctionalPHPAffineSubstitution.row G μ e.val.1, x f.val) + x e = 0 := by
      rw [add_assoc, hsum]
      exact hrow
    exact CharTwo.add_eq_zero.mp hh
  · simp

end SemAC02.Supplement.P2MFunctionalPHPFreeRow
end

section
-- Inlined Solutions.RelativePCFinitePolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePCFinite

theorem pc_polynomial_mul {V : Type} [Finite V] (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (u v : MvPolynomial V (ZMod 2)) (hu : Derivable P U u) (huml : IsMultilinear u)
    (hmem : ∀ w : MvPolynomial V (ZMod 2), w.totalDegree ≤ v.totalDegree → ML (u*w) ∈ U) :
    Derivable P U (ML (u*v)) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    have he : u * C c = c • u := by rw [smul_eq_C_mul, mul_comm]
    rw [he, map_smul, ml_of_multilinear u huml]
    exact pc_smul P U hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add, map_add]
    exact pc_add P U (ihm (fun w hw => hmem w (hw.trans hdm)))
      (ihp (fun w hw => hmem w (hw.trans hdp)))
  | mul_X p i ih =>
    have hle : p.totalDegree ≤ (p * X i).totalDegree := by
      by_cases hp : p = 0
      · simp [hp]
      · rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
    have hi := ih (fun w hw => hmem w (hw.trans hle))
    have he : ML (u * (p * X i)) = ML (X i * ML (u*p)) := by
      rw [ml_mul_right]
      congr 1
      ring
    rw [he]
    apply pc_mul_X P U hi i
    rw [← he]
    exact hmem _ le_rfl

end SemAC02.P2MRelativePCFinite
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
-- Inlined Solutions.P2MLocalBooleanConsequence

set_option maxHeartbeats 3500000

namespace SemAC02.Supplement.P2MLocalBooleanConsequence

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis AC02Frege.P2MMajorityFoundation

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def assignment (S : Finset V) (B : Finset S) : V → ZMod 2 :=
  fun v => if h : v ∈ S then if (⟨v, h⟩ : S) ∈ B then 1 else 0 else 0

noncomputable def indicator (S : Finset V) (B : Finset S) : MvPolynomial V (ZMod 2) :=
  ML (rename Subtype.val (pointPoly B))

theorem indicator_multilinear (S : Finset V) (B : Finset S) : IsMultilinear (indicator S B) := by
  exact ml_multilinear _

theorem indicator_degree (S : Finset V) (B : Finset S) : (indicator S B).totalDegree ≤ S.card := by
  apply (P2MBooleanFlip.ml_totalDegree_le _).trans
  apply (totalDegree_rename_le _ _).trans
  simpa only [Fintype.card_coe] using P2MBooleanLocality.multilinear_degree_le_card (pointPoly B) (pointPoly_multilinear B)

theorem indicator_eval (S : Finset V) (B : Finset S) (x : V → ZMod 2) :
    eval x (indicator S B) = if (fun v : S => x v.val) = (fun v => if v ∈ B then 1 else 0) then 1 else 0 := by
  rw [indicator, eval_ml, eval_rename, pointPoly_eval]
  rfl

theorem eval_local (S : Finset V) (p : MvPolynomial V (ZMod 2)) (hp : p.vars ⊆ S)
    (x y : V → ZMod 2) (hxy : ∀ v ∈ S, x v = y v) : eval x p = eval y p := by
  apply eval₂Hom_congr' rfl _ rfl
  intro v hv hv'
  exact hxy v (hp hv)

theorem assignment_eq (S : Finset V) (B : Finset S) (x : V → ZMod 2)
    (hx : (fun v : S => x v.val) = (fun v => if v ∈ B then 1 else 0)) :
    ∀ v ∈ S, x v = assignment S B v := by
  intro v hv
  have hh := congrFun hx ⟨v, hv⟩
  simpa only [assignment, dif_pos hv] using hh

theorem interpolation (S : Finset V) (q : MvPolynomial V (ZMod 2)) (hml : IsMultilinear q)
    (hvars : q.vars ⊆ S) :
    q = ∑ B : Finset S, eval (assignment S B) q • indicator S B := by
  classical
  apply multilinear_ext hml
    (multilinear_sum _ _ (fun B _ => (mem_restrictDegree V _ 1).mp
      ((restrictDegree V (ZMod 2) 1).smul_mem _ ((mem_restrictDegree V _ 1).mpr (indicator_multilinear S B)))))
  intro x
  have heq (B : Finset S) :
      (fun v : S => x v.val) = (fun v => if v ∈ B then (1 : ZMod 2) else 0) ↔
      B = Finset.univ.filter (fun v : S => x v.val = 1) := by
    constructor
    · intro h
      have hh := congrArg (fun f : S → ZMod 2 => Finset.univ.filter (fun v => f v = 1)) h
      simp only [ones_of_point] at hh
      exact hh.symm
    · intro h
      subst B
      exact (point_of_ones (fun v : S => x v.val)).symm
  simp only [map_sum, smul_eval, indicator_eval, heq]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply eval_local S q hvars
  intro v hv
  dsimp [assignment]
  rw [dif_pos hv]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases eq_zero_or_one (x v) with he | he <;> simp [he]

theorem relative_sum (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) {I : Type} (E : Finset I)
    (f : I → MvPolynomial V (ZMod 2)) (hf : ∀ i ∈ E, P2MRelativePCFinite.Derivable P U (f i)) :
    P2MRelativePCFinite.Derivable P U (∑ i ∈ E, f i) := by
  classical
  induction E using Finset.induction_on with
  | empty => simpa using P2MRelativePCFinite.pc_zero P U
  | @insert i E hi ih =>
    rw [Finset.sum_insert hi]
    exact P2MRelativePCFinite.pc_add P U (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem complete (S : Finset V) (P : Set (MvPolynomial V (ZMod 2))) (a : ℕ)
    (hvars : ∀ p ∈ P, p.vars ⊆ S) (hdegree : ∀ p ∈ P, p.totalDegree ≤ a)
    (q : MvPolynomial V (ZMod 2)) (hml : IsMultilinear q) (hqvars : q.vars ⊆ S)
    (hconsequence : ∀ x : V → ZMod 2, (∀ p ∈ P, eval x p = 0) → eval x q = 0) :
    P2MRelativePCFinite.Derivable P (Ble V (a+S.card)) q := by
  classical
  have hpoint (B : Finset S) :
      P2MRelativePCFinite.Derivable P (Ble V (a+S.card))
        (eval (assignment S B) q • indicator S B) := by
    by_cases hzero : eval (assignment S B) q = 0
    · simpa only [hzero, zero_smul] using P2MRelativePCFinite.pc_zero P (Ble V (a+S.card))
    · have hfExists : ∃ f ∈ P, eval (assignment S B) f ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hzero (hconsequence _ hn)
      obtain ⟨f, hf, hfnz⟩ := hfExists
      have hfval : eval (assignment S B) f = 1 :=
        (eq_zero_or_one _).resolve_left hfnz
      have hFdeg : (ML f).totalDegree ≤ a := (P2MBooleanFlip.ml_totalDegree_le f).trans (hdegree f hf)
      have hFmem : ML f ∈ Ble V (a+S.card) :=
        (P2MBooleanDegreeSpaces.mem_Ble_iff _ _).mpr ⟨ml_multilinear _, hFdeg.trans (Nat.le_add_right _ _)⟩
      have hAx := P2MRelativePCFinite.pc_axiom P (Ble V (a+S.card)) f hf hFmem
      have hProd := P2MRelativePCFinite.pc_polynomial_mul P (Ble V (a+S.card))
        (ML f) (indicator S B) hAx (ml_multilinear _) (by
          intro w hw
          apply (P2MBooleanDegreeSpaces.mem_Ble_iff _ _).mpr
          refine ⟨ml_multilinear _, ?_⟩
          exact (P2MBooleanFlip.ml_totalDegree_le _).trans
            ((totalDegree_mul _ _).trans (Nat.add_le_add hFdeg (hw.trans (indicator_degree S B)))))
      have he : ML (ML f*indicator S B) = indicator S B := by
        apply multilinear_ext (ml_multilinear _) (indicator_multilinear S B)
        intro x
        simp only [eval_ml, map_mul, indicator_eval]
        split_ifs with hx
        · rw [eval_local S f (hvars f hf) x (assignment S B) (assignment_eq S B x hx), hfval]
          simp
        · simp
      rw [he] at hProd
      exact P2MRelativePCFinite.pc_smul P _ hProd _
  rw [interpolation S q hml hqvars]
  exact relative_sum P _ Finset.univ _ (fun B _ => hpoint B)

theorem mono_axioms (P Q : Set (MvPolynomial V (ZMod 2))) (hPQ : P ⊆ Q)
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) (q : MvPolynomial V (ZMod 2))
    (hq : P2MRelativePCFinite.Derivable P U q) : P2MRelativePCFinite.Derivable Q U q := by
  rcases hq with hq | ⟨π, hπ, hspace, hq⟩
  · exact Or.inl hq
  · refine Or.inr ⟨π, ?_, hspace, hq⟩
    intro k hk
    rcases hπ k hk with ⟨p, hp, a, he⟩ | hcomb | hmul
    · exact Or.inl ⟨p, hPQ hp, a, he⟩
    · exact Or.inr (Or.inl hcomb)
    · exact Or.inr (Or.inr hmul)

theorem mono_space (P : Set (MvPolynomial V (ZMod 2)))
    (U W : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) (hUW : U ≤ W)
    (q : MvPolynomial V (ZMod 2)) (hq : P2MRelativePCFinite.Derivable P U q) :
    P2MRelativePCFinite.Derivable P W q := by
  rcases hq with hq | ⟨π, hπ, hspace, hq⟩
  · exact Or.inl hq
  · exact Or.inr ⟨π, hπ, fun p hp => hUW (hspace p hp), hq⟩

end SemAC02.Supplement.P2MLocalBooleanConsequence
end

section
-- Inlined Solutions.P2MPseudoReductionRestriction

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPseudoReductionRestriction

open P2MBooleanDegreeSpaces

lemma ble_mono {V : Type} {k B : ℕ} (h : k≤B) : Ble V k≤Ble V B := by
  intro p hp
  exact (mem_Ble_iff B p).mpr ⟨((mem_Ble_iff k p).mp hp).1,((mem_Ble_iff k p).mp hp).2.trans h⟩

noncomputable def restricted {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) (hk : k≤B) : Ble V k →ₗ[ZMod 2] W :=
  R.comp (Submodule.inclusion (ble_mono hk))

theorem range_eq {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) (hk : k≤B) :
    LinearMap.range (restricted R k hk)=((Submodule.comap (Ble V B).subtype (Ble V k)).map R) := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨Submodule.inclusion (ble_mono hk) p,p.2,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl⟩

theorem rank_eq {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) (hk : k≤B) :
    Module.finrank (ZMod 2) (LinearMap.range (restricted R k hk))=rankLe R k := by
  rw [range_eq]
  rfl

end SemAC02.Supplement.P2MPseudoReductionRestriction
end

section
-- Inlined Solutions.P2MFunctionalPHPEmbeddedSubstitution

set_option maxHeartbeats 3500000

namespace SemAC02.Supplement.P2MFunctionalPHPEmbeddedSubstitution

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MFunctionalPHPMatchingVariables
open P2MFunctionalPHPAffineSubstitution P2MFunctionalPHPRowSemantics

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem field_evaluation (G : PCNonBool.BipGraph L R) (μ : R → L)
    (p : MvPolynomial (Edge (addMatching G μ)) (ZMod 2)) (x : Free G μ → ZMod 2) :
    eval x (sigma G μ p) = eval (fun e => eval x (rho G μ e)) p := by
  change eval x (ML (aeval (rho G μ) p)) = _
  rw [eval_ml, map_aeval]
  have he : (eval x).comp (algebraMap (ZMod 2) (MvPolynomial (Free G μ) (ZMod 2))) =
      RingHom.id (ZMod 2) := by ext a; simp
  rw [he]
  rfl

theorem rho_vars_row (G : PCNonBool.BipGraph L R) (μ : R → L)
    (e : Edge (addMatching G μ)) (f : Free G μ) (hf : f ∈ (rho G μ e).vars) :
    f.val.val.1 = e.val.1 := by
  classical
  unfold rho at hf
  split_ifs at hf with he
  · have hsum := vars_add_subset (1 : MvPolynomial (Free G μ) (ZMod 2)) _ hf
    simp only [vars_one, Finset.empty_union] at hsum
    obtain ⟨g, hg, hfg⟩ := Finset.mem_biUnion.mp (vars_sum_subset _ _ hsum)
    have heq : f = g := by simpa only [vars_X, Finset.mem_singleton] using hfg
    subst f
    exact (Finset.mem_filter.mp hg).2
  · have heq : f = ⟨e, he⟩ := by simpa only [vars_X, Finset.mem_singleton] using hf
    subst f
    rfl

theorem sigma_vars_row (G : PCNonBool.BipGraph L R) (μ : R → L)
    (p : MvPolynomial (Edge (addMatching G μ)) (ZMod 2))
    (f : Free G μ) (hf : f ∈ (sigma G μ p).vars) :
    ∃ e ∈ p.vars, f.val.val.1 = e.val.1 := by
  have hraw := P2MBooleanRestrictions.ml_vars_subset (aeval (rho G μ) p) hf
  rw [aeval_eq_bind₁] at hraw
  obtain ⟨e, he, hfe⟩ := MvPolynomial.mem_vars_bind₁ _ _ hraw
  exact ⟨e, he, rho_vars_row G μ e f hfe⟩

noncomputable def embedded (G : PCNonBool.BipGraph L R) (μ : R → L)
    (p : MvPolynomial (Edge (addMatching G μ)) (ZMod 2)) :
    MvPolynomial (Edge (addMatching G μ)) (ZMod 2) := ML (rename Subtype.val (sigma G μ p))

theorem embedded_vars (G : PCNonBool.BipGraph L R) (μ : R → L)
    (p : MvPolynomial (Edge (addMatching G μ)) (ZMod 2)) (U : Finset L)
    (hp : p.vars ⊆ rowSupport (addMatching G μ) U) :
    (embedded G μ p).vars ⊆ rowSupport (addMatching G μ) U := by
  intro e he
  have hraw := P2MBooleanRestrictions.ml_vars_subset (rename Subtype.val (sigma G μ p)) he
  obtain ⟨f, hf, hfe⟩ := mem_vars_rename Subtype.val (sigma G μ p) hraw
  obtain ⟨g, hg, hrow⟩ := sigma_vars_row G μ p f hf
  apply (mem_rowSupport _ _ _).mpr
  have heRow : e.val.1 = g.val.1 := by rw [← hfe]; exact hrow
  rw [heRow]
  exact (mem_rowSupport _ _ _).mp (hp hg)

theorem embedded_consequence (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (p : MvPolynomial (Edge (addMatching G μ)) (ZMod 2)) (hp : p ∈ fphpG (addMatching G μ))
    (U : Finset L) (hvars : p.vars ⊆ rowSupport (addMatching G μ) U)
    (x : Edge (addMatching G μ) → ZMod 2)
    (hzero : ∀ q ∈ fphpG (addMatching G μ), q.vars ⊆ rowSupport (addMatching G μ) U → eval x q = 0) :
    eval x (embedded G μ p) = 0 := by
  rw [embedded, eval_ml, eval_rename, field_evaluation]
  have heval : eval (fun e => eval (fun f : Free G μ => x f.val) (rho G μ e)) p = eval x p := by
    apply eval₂Hom_congr' rfl _ rfl
    intro e he he'
    exact P2MFunctionalPHPFreeRow.rho_value G μ hμ x e
      (local_row_sum (addMatching G μ) U x hzero e.val.1 ((mem_rowSupport _ _ _).mp (hvars he)))
  change eval (fun e => eval (fun f : Free G μ => x f.val) (rho G μ e)) p = 0
  rw [heval]
  exact hzero p hp hvars

theorem derive_local (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (d : ℕ) (hdegree : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ d)
    (p : MvPolynomial (Edge (addMatching G μ)) (ZMod 2)) (hp : p ∈ fphpG (addMatching G μ))
    (U : Finset L) (hvars : p.vars ⊆ rowSupport (addMatching G μ) U) :
    P2MRelativePCFinite.Derivable (fphpG (addMatching G μ))
      (Ble (Edge (addMatching G μ)) (max 2 d+d*U.card)) (embedded G μ p) := by
  let S := rowSupport (addMatching G μ) U
  let P := {q | q ∈ fphpG (addMatching G μ) ∧ q.vars ⊆ S}
  have hDerive := P2MLocalBooleanConsequence.complete S P (max 2 d)
    (fun q hq => hq.2) (fun q hq => all_degree _ d hdegree q hq.1)
    (embedded G μ p) (ml_multilinear _) (embedded_vars G μ p U hvars) (by
      intro x hx
      exact embedded_consequence G μ hμ p hp U hvars x (fun q hq hqS => hx q ⟨hq, hqS⟩))
  have hDerive' := P2MLocalBooleanConsequence.mono_axioms P (fphpG (addMatching G μ))
    (fun q hq => hq.1) _ _ hDerive
  exact P2MLocalBooleanConsequence.mono_space _ _ _
    (P2MPseudoReductionRestriction.ble_mono (Nat.add_le_add_left (rowSupport_card _ U d hdegree) _)) _ hDerive'

theorem derive_all (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (d : ℕ) (hdegree : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ d)
    (p : MvPolynomial (Edge (addMatching G μ)) (ZMod 2)) (hp : p ∈ fphpG (addMatching G μ)) :
    P2MRelativePCFinite.Derivable (fphpG (addMatching G μ))
      (Ble (Edge (addMatching G μ)) (max 2 d+2*d)) (embedded G μ p) := by
  obtain ⟨U, hU, hvars⟩ := axiom_rows (addMatching G μ) p hp
  exact P2MLocalBooleanConsequence.mono_space _ _ _
    (P2MPseudoReductionRestriction.ble_mono (by nlinarith [Nat.mul_le_mul_left d hU])) _
    (derive_local G μ hμ d hdegree p hp U hvars)

end SemAC02.Supplement.P2MFunctionalPHPEmbeddedSubstitution
end

section
-- Inlined Solutions.P2MFunctionalPHPMatchingDerivation

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MFunctionalPHPMatchingDerivation

open MvPolynomial AC02Frege P2MFunctionalPHPMatchingVariables P2MFunctionalPHPAffineSubstitution

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- Affine matching elimination preserves bounded-degree derivability once the
bounded local axiom certificates fit within the degree budget. -/
theorem derivation (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (d B : ℕ) (hdegree : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ d)
    (hB : max 2 d+2*d ≤ B)
    (π : List (MvPolynomial (Free G μ) (ZMod 2)))
    (hπ : PCNonBool.IsDerivation ML (sigma G μ '' fphpG (addMatching G μ)) π)
    (hπdegree : ∀ p ∈ π, p.totalDegree ≤ B) :
    ∀ p ∈ π, P2MRelativePCFinite.Derivable (fphpG (addMatching G μ))
      (Ble (Edge (addMatching G μ)) B) (P2MRelativePCRenaming.transport Subtype.val p) := by
  apply P2MRelativePCRenaming.derivation Subtype.val _ _ B _ π hπ hπdegree
  rintro q ⟨p, hp, rfl⟩
  exact P2MLocalBooleanConsequence.mono_space _ _ _ (P2MPseudoReductionRestriction.ble_mono hB) _
    (P2MFunctionalPHPEmbeddedSubstitution.derive_all G μ hμ d hdegree p hp)

theorem derivable (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (d B : ℕ) (hdegree : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ d)
    (hB : max 2 d+2*d ≤ B) (p : MvPolynomial (Free G μ) (ZMod 2))
    (hp : P2MRelativePCFinite.Derivable (sigma G μ '' fphpG (addMatching G μ)) (Ble (Free G μ) B) p) :
    P2MRelativePCFinite.Derivable (fphpG (addMatching G μ)) (Ble (Edge (addMatching G μ)) B)
      (P2MRelativePCRenaming.transport Subtype.val p) := by
  rcases hp with rfl | ⟨π, hπ, hmem, hp⟩
  · rw [map_zero]
    exact P2MRelativePCFinite.pc_zero _ _
  · exact derivation G μ hμ d B hdegree hB π hπ
      (fun q hq => ((P2MBooleanDegreeSpaces.mem_Ble_iff B q).mp (hmem q hq)).2) p hp

end SemAC02.Supplement.P2MFunctionalPHPMatchingDerivation
end

section
-- Inlined Solutions.P2MCoveredPolynomialEvaluation

namespace SemAC02.Supplement.P2MCoveredPolynomialEvaluation

open MvPolynomial

theorem evaluation {σ L R : Type} [DecidableEq R] (P : P2MCoveredRep σ L R) (v : R)
    (α y : σ → ZMod 2) (p : MvPolynomial σ (ZMod 2)) :
    eval y (P.substCluster v α p)=eval (fun x => if v ∈ P.cover x then α x else y x) p := by
  classical
  let φ : MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] MvPolynomial σ (ZMod 2) :=
    aeval (fun x => if v ∈ P.cover x then C (α x) else X x)
  have hsub : P.substCluster v α p=φ p := by
    unfold P2MCoveredRep.substCluster
    apply congrArg (fun f : σ → MvPolynomial σ (ZMod 2) => aeval f p)
    funext x
    by_cases h : v ∈ P.cover x <;> simp [φ,h]
  rw [hsub]
  change ((eval y).comp φ.toRingHom) p=(eval (fun x => if v ∈ P.cover x then α x else y x)) p
  apply hom_congr_vars
  · ext a; simp [φ]
  · intro x hx hx'
    by_cases h : v ∈ P.cover x <;> simp [φ,h]
  · rfl

end SemAC02.Supplement.P2MCoveredPolynomialEvaluation
end

section
-- Inlined Solutions.P2MFunctionalPHPCoveredRespectfulness

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPCoveredRespectfulness

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MFunctionalPHPCoveredRepresentation

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def Chosen {G : PCNonBool.BipGraph L R} (u : L) (v : R) (e : Edge G) : Prop :=
  e.val.1 = u ∧ e.val.2 = v

theorem chosen_unique {G : PCNonBool.BipGraph L R} (u : L) (v : R)
    (e f : Edge G) (he : Chosen u v e) (hf : Chosen u v f) : e = f :=
  Subtype.ext (Prod.ext (he.1.trans hf.1.symm) (he.2.trans hf.2.symm))

theorem chosen_touches_conflict (G : PCNonBool.BipGraph L R) (u : L) (v : R) (huv : G.Adj u v)
    (e f : Edge G) (hconflict : Conflict e f) (he : Chosen u v e) :
    v ∈ (representation G).cover f := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases hconflict.2 with hrow | hhole
  · have hf : f.val.1 = u := hrow.symm.trans he.1
    rwa [hf]
  · have hf : f.val.2 = v := hhole.symm.trans he.2
    rw [← hf]
    exact f.property

theorem respectful (G : PCNonBool.BipGraph L R) : (representation G).IsRespectful := by
  classical
  intro J v u hboundary
  have hu : u ∈ J.filter (fun a => (representation G).graph.Adj a v) := by rw [hboundary]; simp
  have huv : G.Adj u v := (graph_iff G u v).mp (Finset.mem_filter.mp hu).2
  let α : Edge G → ZMod 2 := fun e => if Chosen u v e then 1 else 0
  have hzero (e f : Edge G) (hconflict : Conflict e f) : α e*α f = 0 := by
    by_cases he : Chosen u v e <;> by_cases hf : Chosen u v f
    · exact (hconflict.1 (chosen_unique u v e f he hf)).elim
    all_goals simp [α, he, hf]
  refine ⟨α, ?_, ?_⟩
  · intro p hp y
    have hp' : p = P2MCNFExpansionPolynomials.polynomial (rowClause G u) := Set.mem_singleton_iff.mp hp
    rw [hp', P2MCoveredPolynomialEvaluation.evaluation, P2MCNFExpansionPolynomials.polynomial, eval_ml, raw_row, map_prod]
    have hv : v ∈ PCNonBool.nbrOn G Finset.univ u := by simpa [PCNonBool.nbrOn] using huv
    apply Finset.prod_eq_zero (Finset.mem_attach _ ⟨v, hv⟩)
    simp [xE, representation, α, Chosen, hv]
  · rintro g ⟨e, f, hconflict, rfl⟩
    by_cases he : v ∈ (representation G).cover e <;> by_cases hf : v ∈ (representation G).cover f
    · left
      intro y
      rw [P2MCoveredPolynomialEvaluation.evaluation, map_mul, eval_X, eval_X, if_pos he, if_pos hf]
      exact hzero e f hconflict
    · have hnot : ¬ Chosen u v e := fun h => hf (chosen_touches_conflict G u v huv e f hconflict h)
      left
      intro y
      rw [P2MCoveredPolynomialEvaluation.evaluation, map_mul, eval_X, eval_X, if_pos he, if_neg hf]
      simp [α, hnot]
    · have hconflict' : Conflict f e := ⟨hconflict.1.symm, hconflict.2.imp Eq.symm Eq.symm⟩
      have hnot : ¬ Chosen u v f := fun h => he (chosen_touches_conflict G u v huv f e hconflict' h)
      left
      intro y
      rw [P2MCoveredPolynomialEvaluation.evaluation, map_mul, eval_X, eval_X, if_neg he, if_pos hf]
      simp [α, hnot]
    · right
      intro y
      rw [P2MCoveredPolynomialEvaluation.evaluation, map_mul, eval_X, eval_X, if_neg he, if_neg hf, map_mul, eval_X, eval_X]

theorem background_zero (G : PCNonBool.BipGraph L R) :
    ∃ y : Edge G → Bool, ∀ g ∈ (representation G).F0, eval (toF2 y) g = 0 := by
  refine ⟨fun _ => false, ?_⟩
  rintro g ⟨e, f, hconflict, rfl⟩
  simp [toF2]

end SemAC02.Supplement.P2MFunctionalPHPCoveredRespectfulness
end

section
-- Inlined Solutions.P2MBooleanIdealMultilinearization

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MBooleanIdealMultilinearization

open MvPolynomial P2MBooleanAlgebra

lemma power_min {A : Type} [Monoid A] (x : A) (hx : x^2=x) (n : ℕ) : x^min n 1=x^n := by
  have hp : ∀ k : ℕ, x^(k+1)=x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,ih,←pow_two,hx]
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.min_eq_right (by omega : 1 ≤ n+1),pow_one] using (hp n).symm

theorem sub_mem {σ : Type} (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) :
    p-ML p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by
  classical
  let I := Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})
  let q : MvPolynomial σ (ZMod 2) →+* MvPolynomial σ (ZMod 2) ⧸ I := Ideal.Quotient.mk I
  have hX (i : σ) : (q (X i))^2=q (X i) := by
    have hi : X i^2-X i∈I := Ideal.subset_span (Or.inr ⟨i,rfl⟩)
    have hz : q (X i^2-X i)=0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hi
    simpa only [map_sub,map_pow,sub_eq_zero] using hz
  have hmono (s : σ →₀ ℕ) (a : ZMod 2) : q (ML (monomial s a))=q (monomial s a) := by
    rw [ml_monomial,monomial_eq,monomial_eq,map_mul,map_mul]
    congr 1
    simp only [Finsupp.prod,sqfree_support,map_prod,map_pow]
    apply Finset.prod_congr rfl
    intro i hi
    simpa only [sqfree,Finsupp.mapRange_apply] using power_min (q (X i)) (hX i) (s i)
  have he : q (ML p)=q p := by
    conv_lhs => rw [p.as_sum,map_sum,map_sum]
    conv_rhs => rw [p.as_sum,map_sum]
    exact Finset.sum_congr rfl (fun s hs => hmono s (coeff s p))
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change q (p-ML p)=0
  rw [map_sub,he,sub_self]

theorem closed {σ : Type} (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2))
    (hp : p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) :
    ML p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by
  have hh := (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).sub_mem hp (sub_mem G p)
  convert hh using 1 <;> ring

end AC02Frege.P2MBooleanIdealMultilinearization
end

section
-- Inlined Solutions.P2MBooleanLeadingMonomials

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.P2MBooleanLeadingMonomials

open MvPolynomial P2MBooleanAlgebra P2MBooleanBasis
open scoped MonomialOrder

variable {V : Type}

lemma ml_expansion (p : MvPolynomial V (ZMod 2)) :
    ML p = ∑ d ∈ p.support, monomial (sqfree d) (p.coeff d) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum,ml_monomial]

lemma sqfree_le (d : V →₀ ℕ) : sqfree d ≤ d := by
  intro i
  exact min_le_left _ _

lemma degree_ml_le (m : MonomialOrder V) (p : MvPolynomial V (ZMod 2)) :
    m.toSyn (m.degree (ML p)) ≤ m.toSyn (m.degree p) := by
  classical
  apply m.degree_le_iff.mpr
  intro d hd
  rw [ml_expansion] at hd
  obtain ⟨s,hs,hds⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have he : d = sqfree s := Finset.mem_singleton.mp (support_monomial_subset hds)
  rw [he]
  exact (m.toSyn_monotone (sqfree_le s)).trans (m.le_degree hs)

lemma coeff_leading_ml (m : MonomialOrder V) (p : MvPolynomial V (ZMod 2)) (hp : p ≠ 0)
    (hfree : ∀ i, m.degree p i ≤ 1) : coeff (m.degree p) (ML p) = m.leadingCoeff p := by
  classical
  rw [ml_expansion,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (m.degree p)]
  · rw [sqfree_eq_self _ hfree,MvPolynomial.coeff_monomial,if_pos rfl]
    rfl
  · intro d hd hne
    have hs : sqfree d ≠ m.degree p := by
      intro he
      have hle : m.toSyn (m.degree p) ≤ m.toSyn d := by
        rw [← he]
        exact m.toSyn_monotone (sqfree_le d)
      have hd' : d = m.degree p := m.toSyn.injective (le_antisymm (m.le_degree hd) hle)
      exact hne hd'
    simp only [MvPolynomial.coeff_monomial,if_neg hs]
  · intro hnot
    exact False.elim (hnot (m.degree_mem_support hp))

lemma leading_ml {m : MonomialOrder V} {p : MvPolynomial V (ZMod 2)} (hp : p ≠ 0)
    (hfree : ∀ i, m.degree p i ≤ 1) : ML p ≠ 0 ∧ m.degree (ML p) = m.degree p := by
  have hc : coeff (m.degree p) (ML p) ≠ 0 := by
    rw [coeff_leading_ml m p hp hfree]
    exact m.leadingCoeff_ne_zero_iff.mpr hp
  have hn : ML p ≠ 0 := by intro hz; simp [hz] at hc
  refine ⟨hn,m.toSyn.injective (le_antisymm (degree_ml_le m p) (m.le_degree (mem_support_iff.mpr hc)))⟩

lemma indicator_insert [DecidableEq V] {S : Finset V} {v : V} (hv : v ∉ S) :
    Finsupp.indicator S (fun _ _ => (1 : ℕ))+Finsupp.single v 1 =
      Finsupp.indicator (insert v S) (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i = v
  · subst i; simp [Finsupp.indicator_apply,hv]
  · by_cases hS : i ∈ S <;> simp [Finsupp.indicator_apply,hi,hS]

/-- Multiplication by a variable absent from the leading monomial preserves that extension
as the leading monomial after Boolean multilinearization. -/
theorem leading_extension [DecidableEq V] (m : MonomialOrder V) {p : MvPolynomial V (ZMod 2)} (hp : p ≠ 0)
    (S : Finset V) (hS : m.degree p = Finsupp.indicator S (fun _ _ => 1))
    (v : V) (hv : v ∉ S) :
    ML (p*X v) ≠ 0 ∧ m.degree (ML (p*X v)) = Finsupp.indicator (insert v S) (fun _ _ => 1) := by
  classical
  have hX : (X v : MvPolynomial V (ZMod 2)) ≠ 0 := X_ne_zero v
  have hprod : p*X v ≠ 0 := mul_ne_zero hp hX
  have hd : m.degree (p*X v) = Finsupp.indicator (insert v S) (fun _ _ => 1) := by
    rw [m.degree_mul hp hX,m.degree_X,hS,indicator_insert hv]
  have hfree : ∀ i, m.degree (p*X v) i ≤ 1 := by
    intro i
    rw [hd]
    simp only [Finsupp.indicator_apply]
    split_ifs <;> omega
  obtain ⟨hn,he⟩ := leading_ml hprod hfree
  exact ⟨hn,he.trans hd⟩

end AC02Frege.P2MBooleanLeadingMonomials
end

section
-- Inlined Solutions.P2MBooleanIrreducibleDownset

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanIrreducibleDownset

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanLeadingMonomials

variable {σ : Type} [DecidableEq σ]

lemma of_insert (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (S : Finset σ) (v : σ) (hv : v∉S) (h : IsIrred m G (insert v S)) : IsIrred m G S := by
  intro q hq hn he
  have hd : m.degree q=Finsupp.indicator S (fun _ _ => 1) := by
    simpa only [xMon_eq_monomial,m.degree_monomial,if_neg one_ne_zero] using he
  obtain ⟨hp,hdeg⟩ := leading_extension m hn S hd v hv
  have hI := (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).mul_mem_right (X v) hq.2
  have hML := AC02Frege.P2MBooleanIdealMultilinearization.closed G (q*X v) hI
  apply h (ML (q*X v)) ⟨ml_multilinear _,hML⟩ hp
  simpa only [xMon_eq_monomial,m.degree_monomial,if_neg one_ne_zero] using hdeg

theorem subset (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (S T : Finset σ) (hST : S⊆T) (hT : IsIrred m G T) : IsIrred m G S := by
  have hh : ∀ U : Finset σ, Disjoint S U → IsIrred m G (S∪U) → IsIrred m G S := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro hdis h; simpa using h
    | @insert v U hvU ih =>
      intro hdis h
      have hvS : v∉S := by
        intro hv
        exact (Finset.disjoint_left.mp hdis) hv (Finset.mem_insert_self _ _)
      have hv : v∉S∪U := by simpa only [Finset.mem_union,not_or] using And.intro hvS hvU
      have h' : IsIrred m G (S∪U) := by
        apply of_insert m G (S∪U) v hv
        simpa only [Finset.union_insert] using h
      exact ih (Finset.disjoint_of_subset_right (Finset.subset_insert v U) hdis) h'
  apply hh (T\S) (Finset.disjoint_left.mpr (by intro x hx hx'; exact (Finset.mem_sdiff.mp hx').2 hx))
  rwa [Finset.union_sdiff_of_subset hST]

end SemAC02.Supplement.P2MBooleanIrreducibleDownset
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
-- Inlined Solutions.P2MLinearStandardMonomials

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.P2MLinearStandardMonomials

open MvPolynomial
open scoped MonomialOrder

variable {σ : Type}

def Standard (m : MonomialOrder σ) (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (d : σ →₀ ℕ) : Prop := ∀ p ∈ S, p ≠ 0 → m.degree p ≠ d

lemma leadingCoeff_one (m : MonomialOrder σ) {p : MvPolynomial σ (ZMod 2)} (hp : p ≠ 0) :
    m.leadingCoeff p = 1 := by
  have hn := m.leadingCoeff_ne_zero_iff.mpr hp
  generalize m.leadingCoeff p = a at *
  fin_cases a <;> simp_all

lemma cancel_lt (m : MonomialOrder σ) {p q : MvPolynomial σ (ZMod 2)} (hp : p ≠ 0)
    (hq : q ≠ 0) (hd : m.degree q = m.degree p) :
    m.toWithBotSyn (m.withBotDegree (p-q)) < m.toWithBotSyn (m.withBotDegree p) := by
  classical
  rw [m.withBotDegree_lt_withBotDegree_iff]
  by_cases hz : p-q = 0
  · exact Or.inr ⟨hz,hp⟩
  · apply Or.inl
    have hle : m.toSyn (m.degree (p-q)) ≤ m.toSyn (m.degree p) := by
      exact m.degree_sub_le.trans (by rw [hd,max_self])
    apply lt_of_le_of_ne hle
    intro he
    have he' : m.degree (p-q) = m.degree p := m.toSyn.injective he
    have hc : coeff (m.degree p) (p-q) ≠ 0 := by
      rw [← he']
      exact m.coeff_degree_ne_zero_iff.mpr hz
    apply hc
    rw [coeff_sub]
    have hp1 : coeff (m.degree p) p = 1 := leadingCoeff_one m hp
    have hq1 : coeff (m.degree p) q = 1 := by rw [← hd]; exact leadingCoeff_one m hq
    rw [hp1,hq1,sub_self]

/-- Linear elimination modulo an arbitrary subspace, preserving the leading-degree bound.
Unlike polynomial ideal division, this only subtracts scalar multiples of subspace vectors. -/
theorem remainder (m : MonomialOrder σ) (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) :
    ∃ r : MvPolynomial σ (ZMod 2), p-r ∈ S ∧
      m.toWithBotSyn (m.withBotDegree r) ≤ m.toWithBotSyn (m.withBotDegree p) ∧
      ∀ d ∈ r.support, Standard m S d := by
  classical
  have hwf : WellFounded (fun p q : MvPolynomial σ (ZMod 2) =>
      m.toWithBotSyn (m.withBotDegree p) < m.toWithBotSyn (m.withBotDegree q)) :=
    InvImage.wf _ wellFounded_lt
  induction p using hwf.induction with
  | h p ih =>
    by_cases hp : p = 0
    · subst p
      exact ⟨0,by simp,le_rfl,by simp⟩
    by_cases hstd : Standard m S (m.degree p)
    · let t := m.leadingTerm p
      have ht : t ≠ 0 := (m.leadingTerm_eq_zero_iff p).not.mpr hp
      have htd : m.degree t = m.degree p := m.degree_leadingTerm p
      have hlt := cancel_lt m hp ht htd
      obtain ⟨r,hrS,hrle,hrstd⟩ := ih (p-t) hlt
      refine ⟨t+r,?_,?_,?_⟩
      · convert hrS using 1 <;> ring
      · exact (m.withBotDegree_add_le t r).trans (max_le
          (by rw [m.withBotDegree_leadingTerm]) (hrle.trans hlt.le))
      · intro d hd
        have hmem := (Finset.mem_union.mp (MvPolynomial.support_add hd))
        rcases hmem with hdt | hdr
        · have he : d = m.degree p := by simpa only [t,m.support_leadingTerm' hp,Finset.mem_singleton] using hdt
          simpa only [he] using hstd
        · exact hrstd d hdr
    · simp only [Standard,not_forall,_root_.not_imp,not_not] at hstd
      obtain ⟨q,hqS,hq,hqd⟩ := hstd
      have hlt := cancel_lt m hp hq hqd
      obtain ⟨r,hrS,hrle,hrstd⟩ := ih (p-q) hlt
      refine ⟨r,?_,hrle.trans hlt.le,hrstd⟩
      convert S.add_mem hqS hrS using 1 <;> ring

noncomputable def supported (m : MonomialOrder σ)
    (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictSupport (ZMod 2) {d | Standard m S d}

theorem supported_disjoint (m : MonomialOrder σ)
    (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) : Disjoint (supported m S) S := by
  rw [Submodule.disjoint_def]
  intro p hp hpS
  by_contra hn
  exact (hp (m.degree_mem_support hn)) p hpS hn rfl

/-- The graded version used to count leading monomials in a bounded-degree solution space. -/
theorem remainder_totalDegree [LinearOrder σ] [WellFoundedGT σ]
    (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) :
    ∃ r : MvPolynomial σ (ZMod 2), p-r ∈ S ∧ r.totalDegree ≤ p.totalDegree ∧
      ∀ d ∈ r.support, Standard MonomialOrder.degLex S d := by
  classical
  obtain ⟨r,hrS,hrle,hrstd⟩ := remainder MonomialOrder.degLex S p
  refine ⟨r,hrS,?_,hrstd⟩
  exact MvPolynomial.degLex_totalDegree_monotone
    ((MonomialOrder.withBotDegree_le_withBotDegree_iff _ _).mp hrle).1

end AC02Frege.P2MLinearStandardMonomials
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
-- Inlined Solutions.P2MBooleanIdealNormalForm

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanIdealNormalForm

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MExpansionNormalFormFixed

noncomputable def idealSpace {σ : Type} (G : Set (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictDegree σ (ZMod 2) 1 ⊓
    (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).restrictScalars (ZMod 2)

lemma mem_space {σ : Type} (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) :
    p∈idealSpace G ↔ p∈idealB G := by
  change p∈restrictDegree σ (ZMod 2) 1 ∧ p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ↔ _
  rw [mem_restrictDegree]
  rfl

theorem exists_remainder {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    ∃ r∈normalSpan m G, p-r∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ∧ r.totalDegree ≤ p.totalDegree := by
  classical
  obtain ⟨r,hrI,hrle,hrstd⟩ := AC02Frege.P2MLinearStandardMonomials.remainder m (idealSpace G) p
  have hrM : IsMultilinear (p-r) := ((mem_space G _).mp hrI).1
  have hrml : IsMultilinear r := by
    apply (mem_restrictDegree σ r 1).mp
    have hpm := (mem_restrictDegree σ p 1).mpr hp
    have hrm := (mem_restrictDegree σ (p-r) 1).mpr hrM
    convert (restrictDegree σ (ZMod 2) 1).sub_mem hpm hrm using 1 <;> ring
  refine ⟨r,?_,((mem_space G _).mp hrI).2,?_⟩
  · rw [r.as_sum]
    apply Submodule.sum_mem
    intro d hd
    have hfree := hrml d hd
    rw [squarefree_monomial d _ hfree]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨d.support,?_,rfl⟩
    intro q hq hn he
    apply hrstd d hd q ((mem_space G q).mpr hq) hn
    have hlead : m.degree (xMon d.support)=d := by
      rw [xMon_eq_monomial,m.degree_monomial,if_neg one_ne_zero,←squarefree_eq_indicator d hfree]
    exact he.trans hlead
  · apply P2MDegreeCompatibleOrder.totalDegree_mono m hm r p
    exact ((MonomialOrder.withBotDegree_le_withBotDegree_iff _ _).mp hrle).1

theorem unique {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p r q : MvPolynomial σ (ZMod 2)) (hr : r∈normalSpan m G) (hq : q∈normalSpan m G)
    (hpr : p-r∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}))
    (hpq : p-q∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) : r=q := by
  apply sub_eq_zero.mp
  apply zero_of_ideal m G _ ((normalSpan m G).sub_mem hr hq)
  convert (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).sub_mem hpq hpr using 1 <;> ring

theorem spec {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m G p∈normalSpan m G ∧ p-nf m G p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ∧
      (nf m G p).totalDegree ≤ p.totalDegree := by
  obtain ⟨r,hr,hpr,hrdeg⟩ := exists_remainder m hm G p hp
  have hex : ∃ q∈normalSpan m G, p-q∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := ⟨r,hr,hpr⟩
  have hchoice : nf m G p∈normalSpan m G ∧
      p-nf m G p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by
    unfold normalSpan at hex
    simp only [nf,dif_pos hex,normalSpan]
    exact hex.choose_spec
  refine ⟨hchoice.1,hchoice.2,?_⟩
  rw [unique m G p (nf m G p) r hchoice.1 hr hchoice.2 hpr]
  exact hrdeg

end SemAC02.Supplement.P2MBooleanIdealNormalForm
end

section
-- Inlined Solutions.P2MBooleanNormalFormRestrictions

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanNormalFormRestrictions

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MExpansionNormalFormFixed

variable {σ : Type} [DecidableEq σ]

noncomputable def restrict (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2) :
    MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  aeval (fun v => if keep v then X v else C (α v))

theorem monomial (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2) (t : Finset σ) :
    restrict keep α (xMon t)=(∏ v∈t.filter (fun v => ¬ keep v), α v) • xMon (t.filter keep) := by
  rw [restrict,xMon,map_prod]
  simp only [aeval_X]
  rw [smul_eq_C_mul,map_prod,xMon,Finset.prod_filter,Finset.prod_filter,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases h : keep v <;> simp [h]


theorem multilinear (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) : IsMultilinear (restrict keep α p) := by
  apply (mem_restrictDegree σ _ 1).mp
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [AC02Frege.P2MBooleanBasis.squarefree_monomial d _ (hp d hd),map_smul,monomial]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact (mem_restrictDegree σ _ 1).mpr (xMon_multilinear _)

theorem normal_span (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hp : p∈normalSpan m G) : restrict keep α p∈normalSpan m G := by
  change p∈Submodule.span (ZMod 2) (xMon '' {t | IsIrred m G t}) at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    rw [monomial]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨t.filter keep,
      P2MBooleanIrreducibleDownset.subset m G (t.filter keep) t (Finset.filter_subset _ _) ht,rfl⟩
  | zero => rw [map_zero]; exact (normalSpan m G).zero_mem
  | add p q hp hq ihp ihq => rw [map_add]; exact (normalSpan m G).add_mem ihp ihq
  | smul a p hp ih => rw [map_smul]; exact (normalSpan m G).smul_mem a ih

end SemAC02.Supplement.P2MBooleanNormalFormRestrictions
end

section
-- Inlined Solutions.P2MCoveredRestrictionBasics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredRestrictionBasics

open MvPolynomial AC02Frege P2MExpansionNormalFormFixed

variable {σ L R : Type} [DecidableEq σ] [DecidableEq R]

theorem as_restriction (P : P2MCoveredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) :
    P.substCluster v α p = P2MBooleanNormalFormRestrictions.restrict (fun x => v ∉ P.cover x) α p := by
  classical
  unfold P2MCoveredRep.substCluster P2MBooleanNormalFormRestrictions.restrict
  apply congrArg (fun f : σ → MvPolynomial σ (ZMod 2) => aeval f p)
  funext x
  by_cases h : v ∈ P.cover x <;> simp [h]

theorem normal_span (P : P2MCoveredRep σ L R) (m : MonomialOrder σ)
    (G : Set (MvPolynomial σ (ZMod 2))) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hp : p ∈ normalSpan m G) :
    P.substCluster v α p ∈ normalSpan m G := by
  rw [as_restriction]
  exact P2MBooleanNormalFormRestrictions.normal_span m G _ α p hp

theorem multilinear (P : P2MCoveredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) : IsMultilinear (P.substCluster v α p) := by
  rw [as_restriction]
  exact P2MBooleanNormalFormRestrictions.multilinear _ α p hp

theorem untouched (P : P2MCoveredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hvars : ∀ x ∈ p.vars, v ∉ P.cover x) : P.substCluster v α p = p := by
  classical
  let φ : MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] MvPolynomial σ (ZMod 2) :=
    aeval (fun x => if v ∈ P.cover x then C (α x) else X x)
  have hφ : φ p = p := by
    change φ.toRingHom p = RingHom.id (MvPolynomial σ (ZMod 2)) p
    apply MvPolynomial.hom_congr_vars
    · ext a
      simp [φ]
    · intro x hx hx'
      simp [φ, hvars x hx]
    · rfl
  have he : P.substCluster v α p = φ p := by
    unfold P2MCoveredRep.substCluster
    dsimp only [φ]
    apply congrArg (fun f : σ → MvPolynomial σ (ZMod 2) => aeval f p)
    funext x
    by_cases h : v ∈ P.cover x <;> simp [h]
  exact he.trans hφ

theorem sub (P : P2MCoveredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p q : MvPolynomial σ (ZMod 2)) :
    P.substCluster v α (p-q) = P.substCluster v α p - P.substCluster v α q := by
  simp only [as_restriction, map_sub]

theorem monomial_untouched (P : P2MCoveredRep σ L R) (v : R) (α : σ → ZMod 2)
    (t : Finset σ) (hvars : ∀ x ∈ t, v ∉ P.cover x) : P.substCluster v α (xMon t) = xMon t := by
  classical
  unfold P2MCoveredRep.substCluster
  rw [xMon, map_prod]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [aeval_X, if_neg (hvars x hx)]

theorem vars_avoid (P : P2MCoveredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (x : σ) (hx : x ∈ (P.substCluster v α p).vars) : v ∉ P.cover x := by
  classical
  rw [as_restriction] at hx
  unfold P2MBooleanNormalFormRestrictions.restrict at hx
  rw [MvPolynomial.aeval_eq_bind₁] at hx
  obtain ⟨i, hi, hxi⟩ := MvPolynomial.mem_vars_bind₁ _ _ hx
  by_cases h : v ∉ P.cover i
  · simp only [if_pos h, vars_X, Finset.mem_singleton] at hxi
    subst x
    exact h
  · simp only [if_neg h, vars_C, Finset.notMem_empty] at hxi

theorem untouched_axiom [Fintype L] [DecidableEq L]
    (P : P2MCoveredRep σ L R) (u : L) (v : R) (α : σ → ZMod 2)
    (hnot : ¬ P.graph.Adj u v) (p : MvPolynomial σ (ZMod 2)) (hp : p ∈ P.Fu u) :
    P.substCluster v α p = p := by
  apply untouched P v α p
  intro x hx hv
  exact hnot ⟨p, hp, x, hx, hv⟩

theorem background_assignment [Fintype L] [DecidableEq L]
    (P : P2MCoveredRep σ L R) (hP : P.IsRespectful) (v : R) (u : L) (huv : P.graph.Adj u v) :
    ∃ α : σ → ZMod 2, ∀ g ∈ P.F0,
      (∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α g) = 0) ∨
      (∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α g) = eval (toF2 y) g) := by
  obtain ⟨α, hFu, hF0⟩ := hP {u} v u (by simp [huv])
  exact ⟨α, hF0⟩

end SemAC02.Supplement.P2MCoveredRestrictionBasics
end

section
-- Inlined Solutions.P2MCoveredPolynomialAssignment

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredPolynomialAssignment

open MvPolynomial AC02Frege P2MBooleanFunctionPolynomials

theorem assignment {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [DecidableEq R] (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (J : Finset L) (v : R) (u : L)
    (hboundary : J.filter (fun u' => P.graph.Adj u' v)={u}) :
    ∃ α : σ → ZMod 2, (∀ p∈P.Fu u, P.substCluster v α p=0) ∧
      ∀ g∈P.F0, P.substCluster v α g=0 ∨ P.substCluster v α g=g := by
  obtain ⟨α,hFu,hF0⟩ := hP J v u hboundary
  refine ⟨α,?_,?_⟩
  · intro p hp
    have hpml : IsMultilinear p := hml p (Or.inr ⟨u,hp⟩)
    apply multilinear_ext_bool (P2MCoveredRestrictionBasics.multilinear P v α p hpml)
      (by intro s hs; simp at hs)
    intro y
    simpa only [map_zero] using hFu p hp y
  · intro g hg
    have hgml : IsMultilinear g := hml g (Or.inl hg)
    rcases hF0 g hg with hzero | heq
    · left
      apply multilinear_ext_bool (P2MCoveredRestrictionBasics.multilinear P v α g hgml)
        (by intro s hs; simp at hs)
      intro y
      simpa only [map_zero] using hzero y
    · right
      exact multilinear_ext_bool (P2MCoveredRestrictionBasics.multilinear P v α g hgml) hgml heq

end SemAC02.Supplement.P2MCoveredPolynomialAssignment
end

section
-- Inlined Solutions.P2MCoveredLocalIdeals

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredLocalIdeals

open MvPolynomial AC02Frege

variable {σ L R : Type} [DecidableEq σ] [DecidableEq L] [DecidableEq R]

noncomputable def axioms (P : P2MCoveredRep σ L R) (J : Finset L) : Set (MvPolynomial σ (ZMod 2)) :=
  P.F0 ∪ {p | ∃ u∈J, p∈P.Fu u}

noncomputable def ideal (P : P2MCoveredRep σ L R) (J : Finset L) : Ideal (MvPolynomial σ (ZMod 2)) :=
  Ideal.span (axioms P J ∪ {p | ∃ i : σ, p=X i^2-X i})

theorem axioms_mono (P : P2MCoveredRep σ L R) (J K : Finset L) (hJK : J⊆K) : axioms P J⊆axioms P K := by
  rintro p (hp | ⟨u,hu,hp⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨u,hJK hu,hp⟩

theorem ideal_mono (P : P2MCoveredRep σ L R) (J K : Finset L) (hJK : J⊆K) : ideal P J ≤ ideal P K :=
  Ideal.span_mono (Set.union_subset_union_left _ (axioms_mono P J K hJK))

theorem restriction_maps [Fintype L] (P : P2MCoveredRep σ L R) (J : Finset L) (u : L) (v : R)
    (hboundary : J.filter (fun u' => P.graph.Adj u' v)={u}) (α : σ → ZMod 2)
    (hFu : ∀ p∈P.Fu u, P.substCluster v α p=0)
    (hF0 : ∀ g∈P.F0, P.substCluster v α g=0 ∨ P.substCluster v α g=g)
    (q : MvPolynomial σ (ZMod 2)) (hq : q∈ideal P J) : P.substCluster v α q∈ideal P (J.erase u) := by
  let φ := P2MBooleanNormalFormRestrictions.restrict (fun x => v ∉ P.cover x) α
  rw [P2MCoveredRestrictionBasics.as_restriction]
  change φ q∈ideal P (J.erase u)
  have hle : ideal P J ≤ Ideal.comap φ.toRingHom (ideal P (J.erase u)) := by
    apply Ideal.span_le.mpr
    intro p hp
    change φ p∈ideal P (J.erase u)
    rcases hp with (hbg | ⟨u',hu',hp⟩) | ⟨x,rfl⟩
    · change φ p∈ideal P (J.erase u)
      rw [←P2MCoveredRestrictionBasics.as_restriction]
      rcases hF0 p hbg with he | he
      · rw [he]; exact (ideal P (J.erase u)).zero_mem
      · rw [he]; exact Ideal.subset_span (Or.inl (Or.inl hbg))
    · by_cases he : u'=u
      · subst u'
        change P2MBooleanNormalFormRestrictions.restrict _ α p∈_
        rw [←P2MCoveredRestrictionBasics.as_restriction,hFu p hp]
        exact (ideal P (J.erase u)).zero_mem
      · have hnot : ¬ P.graph.Adj u' v := by
          intro hAdj
          have hm : u'∈J.filter (fun a => P.graph.Adj a v) := Finset.mem_filter.mpr ⟨hu',hAdj⟩
          rw [hboundary] at hm
          exact he (Finset.mem_singleton.mp hm)
        change P2MBooleanNormalFormRestrictions.restrict _ α p∈_
        rw [←P2MCoveredRestrictionBasics.as_restriction,P2MCoveredRestrictionBasics.untouched_axiom P u' v α hnot p hp]
        exact Ideal.subset_span (Or.inl (Or.inr ⟨u',Finset.mem_erase.mpr ⟨he,hu'⟩,hp⟩))
    · have hx : φ (X x)=if v ∉ P.cover x then X x else C (α x) := by
        simp only [φ,P2MBooleanNormalFormRestrictions.restrict,aeval_X]
      rw [map_sub,map_pow,hx]
      by_cases h : v ∈ P.cover x
      · rw [if_neg (not_not.mpr h)]
        have hval : (α x)^2=α x := by
          rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (α x) with he | he <;> simp [he]
        rw [←map_pow,hval,sub_self]
        exact (ideal P (J.erase u)).zero_mem
      · rw [if_pos h]
        exact Ideal.subset_span (Or.inr ⟨x,rfl⟩)
  exact hle hq

end SemAC02.Supplement.P2MCoveredLocalIdeals
end

section
-- Inlined Solutions.P2MBooleanNormalSpanMonotonicity

namespace SemAC02.Supplement.P2MBooleanNormalSpanMonotonicity

open MvPolynomial AC02Frege P2MExpansionNormalFormFixed

theorem irreducible {σ : Type} (m : MonomialOrder σ) (G H : Set (MvPolynomial σ (ZMod 2)))
    (hGH : G⊆H) (t : Finset σ) (ht : IsIrred m H t) : IsIrred m G t := by
  intro q hq hn he
  apply ht q ⟨hq.1,?_⟩ hn he
  exact (Ideal.span_mono (Set.union_subset_union_left _ hGH)) hq.2

theorem span {σ : Type} (m : MonomialOrder σ) (G H : Set (MvPolynomial σ (ZMod 2)))
    (hGH : G⊆H) : normalSpan m H ≤ normalSpan m G := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,rfl⟩
  exact Submodule.subset_span ⟨t,irreducible m G H hGH t ht,rfl⟩

end SemAC02.Supplement.P2MBooleanNormalSpanMonotonicity
end

section
-- Inlined Solutions.P2MCoveredNormalFormPeeling

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredNormalFormPeeling

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MExpansionNormalFormFixed P2MBooleanIdealNormalForm P2MCoveredLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L] [DecidableEq R]

theorem peel (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (J : Finset L) (u : L) (v : R) (hboundary : J.filter (fun u' => P.graph.Adj u' v)={u})
    (t : Finset σ) (hvars : ∀ x∈t, v ∉ P.cover x) :
    nf m (axioms P J) (xMon t)=nf m (axioms P (J.erase u)) (xMon t) := by
  obtain ⟨α,hFu,hF0⟩ := P2MCoveredPolynomialAssignment.assignment P hP hml J v u hboundary
  let r := nf m (axioms P J) (xMon t)
  have hr := spec m hm (axioms P J) (xMon t) (xMon_multilinear t)
  have hφr : P.substCluster v α r∈normalSpan m (axioms P J) :=
    P2MCoveredRestrictionBasics.normal_span P m (axioms P J) v α r hr.1
  have hφrSmall : P.substCluster v α r∈normalSpan m (axioms P (J.erase u)) :=
    P2MBooleanNormalSpanMonotonicity.span m _ _ (axioms_mono P (J.erase u) J (Finset.erase_subset _ _)) hφr
  have hmap := restriction_maps P J u v hboundary α hFu hF0 (xMon t-r) hr.2.1
  rw [P2MCoveredRestrictionBasics.sub,P2MCoveredRestrictionBasics.monomial_untouched P v α t hvars] at hmap
  have heBig : r=P.substCluster v α r := unique m (axioms P J) (xMon t) r _ hr.1 hφr hr.2.1
    ((ideal_mono P (J.erase u) J (Finset.erase_subset _ _)) hmap)
  have hrSmall := spec m hm (axioms P (J.erase u)) (xMon t) (xMon_multilinear t)
  have heSmall : nf m (axioms P (J.erase u)) (xMon t)=P.substCluster v α r :=
    unique m _ (xMon t) _ _ hrSmall.1 hφrSmall hrSmall.2.1 hmap
  exact heBig.trans heSmall.symm

end SemAC02.Supplement.P2MCoveredNormalFormPeeling
end

section
-- Inlined Solutions.P2MBoundaryUnion

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MBoundaryUnion

open PCNonBool

variable {L R : Type} [DecidableEq L] [Fintype R] [DecidableEq R]

lemma filter_singleton_of_subset (G : BipGraph L R) (J K : Finset L) (v : R) (u : L)
    (hJK : J⊆K) (hK : K.filter (fun u' => G.Adj u' v)={u}) (hu : u∈J) :
    J.filter (fun u' => G.Adj u' v)={u} := by
  have huK : u∈K.filter (fun u' => G.Adj u' v) := by rw [hK]; simp
  have huv := (Finset.mem_filter.mp huK).2
  apply Finset.Subset.antisymm
  · intro w hw
    have hwK : w∈K.filter (fun u' => G.Adj u' v) := Finset.mem_filter.mpr ⟨hJK (Finset.mem_filter.mp hw).1,(Finset.mem_filter.mp hw).2⟩
    rwa [hK] at hwK
  · intro w hw
    have he : w=u := Finset.mem_singleton.mp hw
    subst w
    exact Finset.mem_filter.mpr ⟨hu,huv⟩

theorem subset (G : BipGraph L R) (J K : Finset L) :
    boundaryOn G Finset.univ (J∪K)⊆boundaryOn G Finset.univ J∪boundaryOn G Finset.univ K := by
  intro v hv
  obtain ⟨u,he⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hv).2
  have hu : u∈(J∪K).filter (fun u' => G.Adj u' v) := by rw [he]; simp
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with huJ | huK
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [filter_singleton_of_subset G J (J∪K) v u Finset.subset_union_left he huJ,Finset.card_singleton]
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [filter_singleton_of_subset G K (J∪K) v u Finset.subset_union_right he huK,Finset.card_singleton]

end P2MProofComplexity.P2MBoundaryUnion
end

section
-- Inlined Solutions.P2MUnionClosedFiniteFamily

namespace P2MProofComplexity.P2MUnionClosedFiniteFamily

variable {V : Type} [DecidableEq V]

theorem union_all_mem (E : Finset (Finset V)) (hzero : ∅∈E)
    (hunion : ∀ A∈E, ∀ B∈E, A∪B∈E) : E.biUnion id∈E := by
  have hh : ∀ T : Finset (Finset V), T⊆E → T.biUnion id∈E := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro h; simpa using hzero
    | @insert A T hAT ih =>
      intro h
      rw [Finset.biUnion_insert]
      exact hunion A (h (Finset.mem_insert_self _ _)) _ (ih (Finset.Subset.trans (Finset.subset_insert A T) h))
  exact hh E Finset.Subset.rfl

end P2MProofComplexity.P2MUnionClosedFiniteFamily
end

section
-- Inlined Solutions.P2MExpansionSmallSupports

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionSmallSupports

open PCNonBool Classical

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem properties (G : BipGraph L R) (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp G s c)
    (A : Finset R) (hA : (A.card : ℝ) ≤ c*s/2) :
    boundaryOn G Finset.univ (supS G s A)⊆A ∧
      ((supS G s A).card : ℝ) ≤ (A.card : ℝ)/c ∧ (A.card : ℝ)/c ≤ s/2 := by
  let E := (Finset.univ : Finset (Finset L)).filter (fun J : Finset L =>
    (J.card : ℝ) ≤ s ∧ boundaryOn G Finset.univ J⊆A)
  have hs : 0 ≤ s := by have hh := Nat.cast_nonneg (α:=ℝ) A.card; nlinarith
  have hzero : ∅∈E := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · simpa only [Finset.card_empty,Nat.cast_zero] using hs
    · simp [boundaryOn]
  have hbound : ∀ J∈E, (J.card : ℝ) ≤ (A.card : ℝ)/c := by
    intro J hJ
    have hh := (Finset.mem_filter.mp hJ).2
    have hb := hexp J hh.1
    have hcard : ((boundaryOn G Finset.univ J).card : ℝ) ≤ A.card := by
      exact_mod_cast Finset.card_le_card hh.2
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  have hhalf : (A.card : ℝ)/c ≤ s/2 := (div_le_iff₀ hc).mpr (by nlinarith)
  have hunion : ∀ J∈E, ∀ K∈E, J∪K∈E := by
    intro J hJ K hK
    have hj := (hbound J hJ).trans hhalf
    have hk := (hbound K hK).trans hhalf
    have hcard : ((J∪K).card : ℝ) ≤ (J.card : ℝ)+(K.card : ℝ) := by
      exact_mod_cast Finset.card_union_le J K
    have hbdry : boundaryOn G Finset.univ (J∪K)⊆A :=
      (P2MProofComplexity.P2MBoundaryUnion.subset G J K).trans (Finset.union_subset
        (Finset.mem_filter.mp hJ).2.2 (Finset.mem_filter.mp hK).2.2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith,hbdry⟩
  have hmem := P2MProofComplexity.P2MUnionClosedFiniteFamily.union_all_mem E hzero hunion
  have he : E.biUnion id=supS G s A := by
    ext u
    simp only [E,supS,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and,id_eq]
  have hprop := (Finset.mem_filter.mp hmem).2
  rw [he] at hprop
  refine ⟨hprop.2,?_,hhalf⟩
  have hh := hbound _ hmem
  rwa [he] at hh

end SemAC02.Supplement.P2MExpansionSmallSupports
end

section
-- Inlined Solutions.P2MExpansionSupportWitness

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionSupportWitness

open PCNonBool

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem contains (G : BipGraph L R) (s : ℝ) (A : Finset R) (J : Finset L)
    (hsize : (J.card : ℝ) ≤ s) (hboundary : boundaryOn G Finset.univ J⊆A) : J⊆supS G s A := by
  classical
  intro u hu
  exact Finset.mem_biUnion.mpr ⟨J,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsize,hboundary⟩,hu⟩

theorem monotone (G : BipGraph L R) (s : ℝ) (A B : Finset R) (hAB : A⊆B) :
    supS G s A⊆supS G s B := by
  classical
  intro u hu
  obtain ⟨J,hJ,huJ⟩ := Finset.mem_biUnion.mp hu
  have hh := (Finset.mem_filter.mp hJ).2
  exact contains G s B J hh.1 (hh.2.trans hAB) huJ

theorem outside_boundary (G : BipGraph L R) (s : ℝ) (A : Finset R)
    (hSup : boundaryOn G Finset.univ (supS G s A)⊆A)
    (J : Finset L) (hSJ : supS G s A⊆J) (hneq : J≠supS G s A) (hsize : (J.card : ℝ) ≤ s) :
    ∃ (u : L) (v : R), u∈J ∧ u∉supS G s A ∧ v∉A ∧ J.filter (fun u' => G.Adj u' v)={u} := by
  classical
  have hnot : ¬ boundaryOn G Finset.univ J⊆A := by
    intro hb
    exact hneq (Finset.Subset.antisymm (contains G s A J hsize hb) hSJ)
  obtain ⟨v,hv,hvA⟩ := Finset.not_subset.mp hnot
  obtain ⟨u,hfilter⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hv).2
  have hu : u∈J.filter (fun u' => G.Adj u' v) := by rw [hfilter]; simp
  have huJ := (Finset.mem_filter.mp hu).1
  have huSup : u∉supS G s A := by
    intro huSup
    have hsingle := P2MProofComplexity.P2MBoundaryUnion.filter_singleton_of_subset G (supS G s A) J v u hSJ hfilter huSup
    have hvSup : v∈boundaryOn G Finset.univ (supS G s A) := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,by rw [hsingle,Finset.card_singleton]⟩
    exact hvA (hSup hvSup)
  exact ⟨u,v,huJ,huSup,hvA,hfilter⟩

end SemAC02.Supplement.P2MExpansionSupportWitness
end

section
-- Inlined Solutions.P2MCoveredNormalFormLocality

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredNormalFormLocality

open MvPolynomial AC02Frege P2MCoveredLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem locality (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c) (t : Finset σ)
    (hsize : ((P.clusters t).card : ℝ) ≤ c*s/2)
    (J : Finset L) (hSJ : supS P.graph s (P.clusters t)⊆J) (hJs : (J.card : ℝ) ≤ s) :
    nf m (axioms P J) (xMon t)=P2MCoveredRep.expOp P m s t := by
  have hSup := (P2MExpansionSmallSupports.properties P.graph s c hc hexp (P.clusters t) hsize).1
  have hh : ∀ j : ℕ, ∀ J : Finset L, J.card=j → supS P.graph s (P.clusters t)⊆J →
      (J.card : ℝ) ≤ s → nf m (axioms P J) (xMon t)=P2MCoveredRep.expOp P m s t := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro J hj hSJ hJs
      by_cases he : J=supS P.graph s (P.clusters t)
      · subst J
        rfl
      obtain ⟨u,v,hu,huSup,hvA,hboundary⟩ :=
        P2MExpansionSupportWitness.outside_boundary P.graph s (P.clusters t) hSup J hSJ he hJs
      have hvars : ∀ x∈t, v ∉ P.cover x := by
        intro x hx heq
        exact hvA ((P2MCoveredRep.mem_clusters P t v).mpr ⟨x,hx,heq⟩)
      have hpeel := P2MCoveredNormalFormPeeling.peel P hP hml m hm J u v hboundary t hvars
      have hcard : (J.erase u).card < j := by
        have hlt : (J.erase u).card < J.card := Finset.card_lt_card (Finset.erase_ssubset hu)
        exact hlt.trans_eq hj
      have hSJerase : supS P.graph s (P.clusters t)⊆J.erase u := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨by intro heq; subst a; exact huSup ha,hSJ ha⟩
      have hJsmall : ((J.erase u).card : ℝ) ≤ s := by
        have hle : ((J.erase u).card : ℝ) ≤ J.card := by exact_mod_cast Finset.card_le_card (Finset.erase_subset u J)
        exact hle.trans hJs
      exact hpeel.trans (ih (J.erase u).card hcard (J.erase u) rfl hSJerase hJsmall)
  exact hh J.card J rfl hSJ hJs

end SemAC02.Supplement.P2MCoveredNormalFormLocality
end

section
-- Inlined Solutions.P2MCoveredLocalIdealStability

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredLocalIdealStability

open MvPolynomial AC02Frege P2MCoveredLocalIdeals

variable {σ L R : Type} [DecidableEq σ] [DecidableEq L] [DecidableEq R]

theorem stable [Fintype L] (P : P2MCoveredRep σ L R) (J : Finset L) (v : R)
    (hnot : ∀ u∈J, ¬ P.graph.Adj u v) (α : σ → ZMod 2)
    (hF0 : ∀ g∈P.F0, P.substCluster v α g=0 ∨ P.substCluster v α g=g)
    (q : MvPolynomial σ (ZMod 2)) (hq : q∈ideal P J) : P.substCluster v α q∈ideal P J := by
  let φ := P2MBooleanNormalFormRestrictions.restrict (fun x => v ∉ P.cover x) α
  rw [P2MCoveredRestrictionBasics.as_restriction]
  change φ q∈ideal P J
  have hle : ideal P J ≤ Ideal.comap φ.toRingHom (ideal P J) := by
    apply Ideal.span_le.mpr
    intro p hp
    change φ p∈ideal P J
    rcases hp with (hbg | ⟨u,hu,hp⟩) | ⟨x,rfl⟩
    · rw [←P2MCoveredRestrictionBasics.as_restriction]
      rcases hF0 p hbg with he | he
      · rw [he]; exact (ideal P J).zero_mem
      · rw [he]; exact Ideal.subset_span (Or.inl (Or.inl hbg))
    · change P2MBooleanNormalFormRestrictions.restrict _ α p∈_
      rw [←P2MCoveredRestrictionBasics.as_restriction,P2MCoveredRestrictionBasics.untouched_axiom P u v α (hnot u hu) p hp]
      exact Ideal.subset_span (Or.inl (Or.inr ⟨u,hu,hp⟩))
    · have hx : φ (X x)=if v ∉ P.cover x then X x else C (α x) := by
        simp only [φ,P2MBooleanNormalFormRestrictions.restrict,aeval_X]
      rw [map_sub,map_pow,hx]
      by_cases h : v ∈ P.cover x
      · rw [if_neg (not_not.mpr h)]
        have hval : (α x)^2=α x := by
          rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (α x) with he | he <;> simp [he]
        rw [←map_pow,hval,sub_self]
        exact (ideal P J).zero_mem
      · rw [if_pos h]
        exact Ideal.subset_span (Or.inr ⟨x,rfl⟩)
  exact hle hq

end SemAC02.Supplement.P2MCoveredLocalIdealStability
end

section
-- Inlined Solutions.P2MCoveredNormalFormVariables

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredNormalFormVariables

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MCoveredLocalIdeals P2MBooleanIdealNormalForm

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L] [DecidableEq R]

theorem absent (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (J : Finset L) (t : Finset σ) (v : R) (u₀ : L) (hactive : P.graph.Adj u₀ v)
    (hnot : ∀ u∈J, ¬ P.graph.Adj u v) (hvars : ∀ x∈t, v ∉ P.cover x) :
    ∀ x∈(nf m (axioms P J) (xMon t)).vars, v ∉ P.cover x := by
  obtain ⟨α,hFu,hF0⟩ := P2MCoveredPolynomialAssignment.assignment P hP hml {u₀} v u₀ (by simp [hactive])
  let r := nf m (axioms P J) (xMon t)
  have hr := spec m hm (axioms P J) (xMon t) (xMon_multilinear t)
  have hpr := P2MCoveredRestrictionBasics.normal_span P m (axioms P J) v α r hr.1
  have hmap := P2MCoveredLocalIdealStability.stable P J v hnot α hF0 (xMon t-r) hr.2.1
  rw [P2MCoveredRestrictionBasics.sub,P2MCoveredRestrictionBasics.monomial_untouched P v α t hvars] at hmap
  have he : r=P.substCluster v α r := unique m (axioms P J) (xMon t) r _ hr.1 hpr hr.2.1 hmap
  intro x hx
  change x∈r.vars at hx
  rw [he] at hx
  exact P2MCoveredRestrictionBasics.vars_avoid P v α r x hx

theorem active_locality (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (J : Finset L) (t : Finset σ) (x : σ) (hx : x∈(nf m (axioms P J) (xMon t)).vars)
    (v : R) (hv : v ∈ P.cover x) (u₀ : L) (hactive : P.graph.Adj u₀ v) :
    (∃ u ∈ J, P.graph.Adj u v) ∨ v ∈ P.clusters t := by
  by_cases hJ : ∃ u ∈ J, P.graph.Adj u v
  · exact Or.inl hJ
  · right
    by_contra hinput
    have hnot : ∀ u ∈ J, ¬ P.graph.Adj u v := by
      intro u hu hAdj
      exact hJ ⟨u, hu, hAdj⟩
    have hvars : ∀ y ∈ t, v ∉ P.cover y := by
      intro y hy he
      exact hinput ((P2MCoveredRep.mem_clusters P t v).mpr ⟨y, hy, he⟩)
    exact absent P hP hml m hm J t v u₀ hactive hnot hvars x hx hv

end SemAC02.Supplement.P2MCoveredNormalFormVariables
end

section
-- Inlined Solutions.P2MCoveredMonomialNormalForms

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredMonomialNormalForms

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
    P2MExpansionNormalFormFixed P2MCoveredLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem normal_span (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) : P2MCoveredRep.expOp P m s t∈P2MExpansionNormalFormFixed.normalSpan m
      (axioms P (supS P.graph s (P.clusters t))) :=
  (P2MBooleanIdealNormalForm.spec m hm _ (xMon t) (xMon_multilinear t)).1

theorem multilinear (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) : IsMultilinear (P2MCoveredRep.expOp P m s t) :=
  normal_multilinear m _ _ (normal_span P m hm s t)

theorem degree (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) : (P2MCoveredRep.expOp P m s t).totalDegree ≤ t.card := by
  have hh := (P2MBooleanIdealNormalForm.spec m hm (axioms P (supS P.graph s (P.clusters t)))
    (xMon t) (xMon_multilinear t)).2.2
  exact hh.trans_eq (AC02Frege.P2MBooleanAlgebra.xMon_totalDegree t)

theorem support_card (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) (d : σ →₀ ℕ) (hd : d∈(P2MCoveredRep.expOp P m s t).support) : d.support.card ≤ t.card := by
  rw [←squarefree_sum d (multilinear P m hm s t d hd)]
  exact (le_totalDegree hd).trans (degree P m hm s t)

theorem active_locality (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) (x : σ) (hx : x∈(P2MCoveredRep.expOp P m s t).vars)
    (v : R) (hv : v ∈ P.cover x) (u : L) (hu : P.graph.Adj u v) :
    (∃ u ∈ supS P.graph s (P.clusters t), P.graph.Adj u v) ∨ v ∈ P.clusters t :=
  P2MCoveredNormalFormVariables.active_locality P hP hml m hm _ t x hx v hv u hu

end SemAC02.Supplement.P2MCoveredMonomialNormalForms
end

section
-- Inlined Solutions.P2MExpansionSupportClosure

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionSupportClosure

open PCNonBool

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem boundary_control (G : BipGraph L R) (J K : Finset L) (A B : Finset R)
    (hJ : boundaryOn G Finset.univ J⊆B) (hK : boundaryOn G Finset.univ K⊆A)
    (hB : ∀ v∈B, (∃ u, G.Adj u v) → v∈A ∨ ∃ u∈K, G.Adj u v) :
    boundaryOn G Finset.univ (J∪K)⊆A := by
  intro v hv
  obtain ⟨u,he⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hv).2
  have hu : u∈(J∪K).filter (fun u' => G.Adj u' v) := by rw [he]; simp
  have huv := (Finset.mem_filter.mp hu).2
  by_cases huK : u∈K
  · apply hK
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [P2MProofComplexity.P2MBoundaryUnion.filter_singleton_of_subset G K (J∪K) v u
      Finset.subset_union_right he huK,Finset.card_singleton]
  · have huJ : u∈J := (Finset.mem_union.mp (Finset.mem_filter.mp hu).1).resolve_right huK
    have hvJ : v∈boundaryOn G Finset.univ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      rw [P2MProofComplexity.P2MBoundaryUnion.filter_singleton_of_subset G J (J∪K) v u
        Finset.subset_union_left he huJ,Finset.card_singleton]⟩
    rcases hB v (hJ hvJ) ⟨u,huv⟩ with hvA | ⟨u',hu'K,hu'v⟩
    · exact hvA
    · have hu' : u'∈(J∪K).filter (fun a => G.Adj a v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hu'K,hu'v⟩
      rw [he] at hu'
      have heq : u'=u := Finset.mem_singleton.mp hu'
      subst u'
      exact (huK hu'K).elim

theorem support_subset (G : BipGraph L R) (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp G s c)
    (A B : Finset R) (hA : (A.card : ℝ) ≤ c*s/2) (hBsize : (B.card : ℝ) ≤ c*s/2)
    (hB : ∀ v∈B, (∃ u, G.Adj u v) → v∈A ∨ ∃ u∈supS G s A, G.Adj u v) :
    supS G s B⊆supS G s A := by
  have hSA := P2MExpansionSmallSupports.properties G s c hc hexp A hA
  have hSB := P2MExpansionSmallSupports.properties G s c hc hexp B hBsize
  have hbdry := boundary_control G (supS G s B) (supS G s A) A B hSB.1 hSA.1 hB
  have hcard : (((supS G s B)∪(supS G s A)).card : ℝ) ≤ s := by
    have hu : (((supS G s B)∪(supS G s A)).card : ℝ) ≤
        ((supS G s B).card : ℝ)+((supS G s A).card : ℝ) := by exact_mod_cast Finset.card_union_le _ _
    have ha := hSA.2.1.trans hSA.2.2
    have hb := hSB.2.1.trans hSB.2.2
    linarith
  exact Finset.subset_union_left.trans (P2MExpansionSupportWitness.contains G s A _ hcard hbdry)

end SemAC02.Supplement.P2MExpansionSupportClosure
end

section
-- Inlined Solutions.P2MCoveredMultiplicationSupport

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MCoveredMultiplicationSupport

open MvPolynomial AC02Frege P2MCoveredLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem support_subset (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p ∈ P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (t : Finset σ) (hbudget : (overlap : ℝ)*((t.card : ℝ)+1) ≤ c*s/2)
    (d : σ →₀ ℕ) (hd : d ∈ (P2MCoveredRep.expOp P m s t).support) (x : σ) :
    supS P.graph s (P.clusters (insert x d.support)) ⊆
      supS P.graph s (P.clusters (insert x t)) := by
  let A := P.clusters (insert x t)
  let B := P.clusters (insert x d.support)
  have hdt := P2MCoveredMonomialNormalForms.support_card P m hm s t d hd
  have hA : (A.card : ℝ) ≤ c*s/2 := (P.clusters_insert_bound overlap hoverlap t x).trans hbudget
  have hB : (B.card : ℝ) ≤ c*s/2 := by
    have hh := P.clusters_insert_bound overlap hoverlap d.support x
    have hdtR : (d.support.card : ℝ) ≤ t.card := by exact_mod_cast hdt
    have hdt1 : (d.support.card : ℝ)+1 ≤ (t.card : ℝ)+1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hdt1 (Nat.cast_nonneg overlap : (0 : ℝ) ≤ overlap)
    exact hh.trans (hmul.trans hbudget)
  apply P2MExpansionSupportClosure.support_subset P.graph s c hc hexp A B hA hB
  intro v hv hactive
  obtain ⟨y, hy, hvy⟩ := (P2MCoveredRep.mem_clusters P _ v).mp hv
  rcases Finset.mem_insert.mp hy with he | hy
  · subst y
    left
    exact (P2MCoveredRep.mem_clusters P _ v).mpr ⟨x, Finset.mem_insert_self _ _, hvy⟩
  · obtain ⟨u, hu⟩ := hactive
    have hyv : y ∈ (P2MCoveredRep.expOp P m s t).vars := (mem_vars_iff_mem_support _).mpr ⟨d, hd, hy⟩
    rcases P2MCoveredMonomialNormalForms.active_locality P hP hml m hm s t y hyv v hvy u hu with
      ⟨u', hu', hu'v⟩ | hyA
    · right
      exact ⟨u', P2MExpansionSupportWitness.monotone P.graph s _ A
        (P.clusters_mono (Finset.subset_insert x t)) hu', hu'v⟩
    · left
      exact P.clusters_mono (Finset.subset_insert x t) hyA

theorem local_reduction (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p ∈ P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (t : Finset σ) (hbudget : (overlap : ℝ)*((t.card : ℝ)+1) ≤ c*s/2)
    (d : σ →₀ ℕ) (hd : d ∈ (P2MCoveredRep.expOp P m s t).support) (x : σ) :
    P2MCoveredRep.expOp P m s (insert x d.support) =
      nf m (axioms P (supS P.graph s (P.clusters (insert x t)))) (xMon (insert x d.support)) := by
  have hdt := P2MCoveredMonomialNormalForms.support_card P m hm s t d hd
  have hA : ((P.clusters (insert x t)).card : ℝ) ≤ c*s/2 :=
    (P.clusters_insert_bound overlap hoverlap t x).trans hbudget
  have hB : ((P.clusters (insert x d.support)).card : ℝ) ≤ c*s/2 := by
    have hh := P.clusters_insert_bound overlap hoverlap d.support x
    have hdtR : (d.support.card : ℝ) ≤ t.card := by exact_mod_cast hdt
    have hdt1 : (d.support.card : ℝ)+1 ≤ (t.card : ℝ)+1 := by linarith
    exact hh.trans ((mul_le_mul_of_nonneg_left hdt1
      (Nat.cast_nonneg overlap : (0 : ℝ) ≤ overlap)).trans hbudget)
  have hProps := P2MExpansionSmallSupports.properties P.graph s c hc hexp (P.clusters (insert x t)) hA
  have hsize : ((supS P.graph s (P.clusters (insert x t))).card : ℝ) ≤ s := by
    have hh := hProps.2.1.trans hProps.2.2
    have hs : 0 ≤ s := by
      have hz := Nat.cast_nonneg (α:=ℝ) (P.clusters (insert x t)).card
      nlinarith
    linarith
  exact (P2MCoveredNormalFormLocality.locality P hP hml m hm s c hc hexp (insert x d.support) hB _
    (support_subset P hP hml m hm overlap hoverlap s c hc hexp t hbudget d hd x) hsize).symm

end SemAC02.Supplement.P2MCoveredMultiplicationSupport
end

section
-- Inlined Solutions.P2MCoveredLinearMap

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredLinearMap

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

noncomputable def operator (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (s : ℝ) :
    MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  (basisMonomials σ (ZMod 2)).constr (ZMod 2) (fun d => P2MCoveredRep.expOp P m s d.support)

theorem monomial (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (s : ℝ)
    (d : σ →₀ ℕ) (a : ZMod 2) : operator P m s (MvPolynomial.monomial d a)=a • P2MCoveredRep.expOp P m s d.support := by
  have h := (basisMonomials σ (ZMod 2)).constr_basis (ZMod 2)
    (fun d => P2MCoveredRep.expOp P m s d.support) d
  have ha : MvPolynomial.monomial d a=a • MvPolynomial.monomial d (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
  rw [ha,map_smul]
  exact congrArg (fun p => a • p) h

theorem xMon (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (t : Finset σ) :
    operator P m s (AC02Frege.xMon t)=P2MCoveredRep.expOp P m s t := by
  rw [xMon_eq_monomial,monomial,one_smul,indicator_support]

theorem multilinear (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (p : MvPolynomial σ (ZMod 2)) : IsMultilinear (operator P m s p) := by
  classical
  apply (mem_restrictDegree σ _ 1).mp
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [monomial]
  apply Submodule.smul_mem
  exact (mem_restrictDegree σ _ 1).mpr (P2MCoveredMonomialNormalForms.multilinear P m hm s _)

theorem degree (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (p : MvPolynomial σ (ZMod 2)) : (operator P m s p).totalDegree ≤ p.totalDegree := by
  classical
  have he : operator P m s p=∑ d∈p.support, operator P m s (MvPolynomial.monomial d (coeff d p)) := by
    exact congrArg (operator P m s) p.as_sum |>.trans (map_sum _ _ _)
  apply (mem_restrictTotalDegree σ _ _).mp
  rw [he]
  apply Submodule.sum_mem
  intro d hd
  rw [monomial]
  apply (mem_restrictTotalDegree σ _ _).mpr
  apply (totalDegree_smul_le _ _).trans
  apply (P2MCoveredMonomialNormalForms.degree P m hm s d.support).trans
  apply le_trans _ (le_totalDegree hd)
  change d.support.card ≤ ∑ i∈d.support, d i
  calc
    d.support.card = ∑ _i∈d.support, 1 := by simp
    _ ≤ ∑ i∈d.support, d i := Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem ml (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (s : ℝ)
    (p : MvPolynomial σ (ZMod 2)) : operator P m s (ML p)=operator P m s p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a => rw [ml_monomial,monomial,monomial,sqfree_support]
  | add p q hp hq => simp only [map_add,hp,hq]

end SemAC02.Supplement.P2MCoveredLinearMap
end

section
-- Inlined Solutions.P2MBooleanNormalFormAlgebra

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanNormalFormAlgebra

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MExpansionNormalFormFixed P2MBooleanIdealNormalForm

variable {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (G : Set (MvPolynomial σ (ZMod 2)))

include hm

theorem congruent (p q : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (hq : IsMultilinear q)
    (hpq : p-q∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) : nf m G p=nf m G q := by
  have hnp := spec m hm G p hp
  have hnq := spec m hm G q hq
  apply unique m G p _ _ hnp.1 hnq.1 hnp.2.1
  convert (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).add_mem hpq hnq.2.1 using 1 <;> ring

theorem zero : nf m G 0=0 := by
  have hml : IsMultilinear (0 : MvPolynomial σ (ZMod 2)) := by intro s hs; simp at hs
  have hs := spec m hm G 0 hml
  apply unique m G 0 _ 0 hs.1 (normalSpan m G).zero_mem hs.2.1
  simp

theorem of_ideal (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p)
    (hI : p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) : nf m G p=0 := by
  have hz : IsMultilinear (0 : MvPolynomial σ (ZMod 2)) := by intro d hd; simp at hd
  have he : p-0∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by simpa using hI
  exact (congruent m hm G p 0 hp hz he).trans (zero m hm G)

theorem add (p q : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (hq : IsMultilinear q) :
    nf m G (p+q)=nf m G p+nf m G q := by
  have hpM := (mem_restrictDegree σ p 1).mpr hp
  have hqM := (mem_restrictDegree σ q 1).mpr hq
  have hs := spec m hm G (p+q) ((mem_restrictDegree σ _ 1).mp
    ((restrictDegree σ (ZMod 2) 1).add_mem hpM hqM))
  have hnp := spec m hm G p hp
  have hnq := spec m hm G q hq
  apply unique m G (p+q) _ _ hs.1 ((normalSpan m G).add_mem hnp.1 hnq.1) hs.2.1
  convert (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).add_mem hnp.2.1 hnq.2.1 using 1 <;> ring

theorem scalar (a : ZMod 2) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m G (a • p)=a • nf m G p := by
  have hpM := (mem_restrictDegree σ p 1).mpr hp
  have hs := spec m hm G (a • p) ((mem_restrictDegree σ _ 1).mp
    ((restrictDegree σ (ZMod 2) 1).smul_mem a hpM))
  have hnp := spec m hm G p hp
  apply unique m G (a • p) _ _ hs.1 ((normalSpan m G).smul_mem a hnp.1) hs.2.1
  have hh := (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).mul_mem_left (C a) hnp.2.1
  simpa only [smul_eq_C_mul,mul_sub] using hh

theorem nested (H : Set (MvPolynomial σ (ZMod 2))) (hGH : G⊆H)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m H (nf m G p)=nf m H p := by
  have hs := spec m hm G p hp
  apply congruent m hm H _ p (normal_multilinear m G _ hs.1) hp
  have hI : Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ≤
      Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i}) :=
    Ideal.span_mono (Set.union_subset_union_left _ hGH)
  have hh := (Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i})).neg_mem (hI hs.2.1)
  simpa only [neg_sub] using hh

theorem sum {ι : Type} (S : Finset ι) (p : ι → MvPolynomial σ (ZMod 2))
    (hp : ∀ i∈S, IsMultilinear (p i)) : nf m G (∑ i∈S, p i)=∑ i∈S, nf m G (p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,zero m hm G]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,add m hm G _ _ (hp i (Finset.mem_insert_self _ _))]
    · rw [ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]
    · apply (mem_restrictDegree σ _ 1).mp
      exact Submodule.sum_mem _ (fun j hj => (mem_restrictDegree σ _ 1).mpr (hp j (Finset.mem_insert_of_mem hj)))

theorem expansion (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m G p=∑ d∈p.support, coeff d p • nf m G (xMon d.support) := by
  classical
  have he : p=∑ d∈p.support, coeff d p • xMon d.support :=
    p.as_sum.trans (Finset.sum_congr rfl (fun d hd => AC02Frege.P2MBooleanBasis.squarefree_monomial d _ (hp d hd)))
  calc
    nf m G p = nf m G (∑ d∈p.support, coeff d p • xMon d.support) := congrArg (nf m G) he
    _ = ∑ d∈p.support, nf m G (coeff d p • xMon d.support) := sum m hm G _ _ (fun d _ =>
      (mem_restrictDegree σ _ 1).mp ((restrictDegree σ (ZMod 2) 1).smul_mem _
        ((mem_restrictDegree σ _ 1).mpr (AC02Frege.P2MBooleanAlgebra.xMon_multilinear _))))
    _ = _ := Finset.sum_congr rfl (fun d _ => scalar m hm G _ _ (AC02Frege.P2MBooleanAlgebra.xMon_multilinear _))

end SemAC02.Supplement.P2MBooleanNormalFormAlgebra
end

section
-- Inlined Solutions.P2MCoveredPolynomialLocality

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredPolynomialLocality

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MCoveredLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem eq_nf (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p)
    (hlocal : ∀ d∈p.support, P2MCoveredRep.expOp P m s d.support=nf m G (xMon d.support)) :
    P2MCoveredLinearMap.operator P m s p=nf m G p := by
  classical
  have he := congrArg (P2MCoveredLinearMap.operator P m s) p.as_sum
  rw [map_sum] at he
  rw [he,P2MBooleanNormalFormAlgebra.expansion m hm G p hp]
  exact Finset.sum_congr rfl (fun d hd => by rw [P2MCoveredLinearMap.monomial,hlocal d hd])

theorem variable_sum (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (s : ℝ)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (x : σ) :
    P2MCoveredLinearMap.operator P m s (ML (X x*p))=
      ∑ d∈p.support, coeff d p • P2MCoveredRep.expOp P m s (insert x d.support) := by
  classical
  let M := P2MCoveredLinearMap.operator P m s |>.comp (ML.comp (LinearMap.mulLeft (ZMod 2) (X x)))
  have he : p=∑ d∈p.support, coeff d p • xMon d.support :=
    p.as_sum.trans (Finset.sum_congr rfl (fun d hd => squarefree_monomial d _ (hp d hd)))
  have hh := congrArg M he
  rw [map_sum] at hh
  dsimp only [M,LinearMap.comp_apply,LinearMap.mulLeft_apply] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_smul_comm,map_smul,map_smul]
  rw [AC02Frege.P2MBooleanVariableProducts.monomial_insert,P2MCoveredLinearMap.xMon]

theorem variable_eq_nf (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (x : σ)
    (hlocal : ∀ d∈p.support, P2MCoveredRep.expOp P m s (insert x d.support)=nf m G (xMon (insert x d.support))) :
    P2MCoveredLinearMap.operator P m s (ML (X x*p))=nf m G (ML (X x*p)) := by
  classical
  rw [variable_sum P m s p hp x]
  let M := ML.comp (LinearMap.mulLeft (ZMod 2) (X x))
  have he : p=∑ d∈p.support, coeff d p • xMon d.support :=
    p.as_sum.trans (Finset.sum_congr rfl (fun d hd => squarefree_monomial d _ (hp d hd)))
  have hh := congrArg M he
  rw [map_sum] at hh
  have hsum : ML (X x*p)=∑ d∈p.support, coeff d p • xMon (insert x d.support) := by
    dsimp only [M,LinearMap.comp_apply,LinearMap.mulLeft_apply] at hh
    exact hh.trans (Finset.sum_congr rfl (fun d _ => by
      rw [mul_smul_comm,map_smul]
      rw [AC02Frege.P2MBooleanVariableProducts.monomial_insert]))
  rw [hsum,P2MBooleanNormalFormAlgebra.sum m hm G]
  · exact Finset.sum_congr rfl (fun d hd => (congrArg (fun q => coeff d p • q) (hlocal d hd)).trans
      (P2MBooleanNormalFormAlgebra.scalar m hm G _ _ (xMon_multilinear _)).symm)
  · intro d hd
    exact (mem_restrictDegree σ _ 1).mp ((restrictDegree σ (ZMod 2) 1).smul_mem _
      ((mem_restrictDegree σ _ 1).mpr (xMon_multilinear _)))

end SemAC02.Supplement.P2MCoveredPolynomialLocality
end

section
-- Inlined Solutions.P2MBooleanNormalFormMultiplication

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanNormalFormMultiplication

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

theorem nested_product {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (G H : Set (MvPolynomial σ (ZMod 2))) (hGH : G⊆H)
    (f p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m H (ML (f*nf m G p))=nf m H (ML (f*p)) := by
  apply P2MBooleanNormalFormAlgebra.congruent m hm H _ _ (ml_multilinear _) (ml_multilinear _)
  rw [←map_sub]
  have hI : Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ≤
      Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i}) :=
    Ideal.span_mono (Set.union_subset_union_left _ hGH)
  have hdiff := (Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i})).neg_mem
    (hI (P2MBooleanIdealNormalForm.spec m hm G p hp).2.1)
  have hprod := (Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i})).mul_mem_left f hdiff
  apply AC02Frege.P2MBooleanIdealMultilinearization.closed
  convert hprod using 1 <;> ring

end SemAC02.Supplement.P2MBooleanNormalFormMultiplication
end

section
-- Inlined Solutions.P2MCoveredMultiplicationIdentity

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredMultiplicationIdentity

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MCoveredLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem monomial (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (t : Finset σ) (hbudget : (overlap : ℝ)*((t.card : ℝ)+1) ≤ c*s/2) (x : σ) :
    P2MCoveredLinearMap.operator P m s (ML (X x*P2MCoveredRep.expOp P m s t))=P2MCoveredRep.expOp P m s (insert x t) := by
  let J := supS P.graph s (P.clusters t)
  let K := supS P.graph s (P.clusters (insert x t))
  have hJK : J⊆K := P2MExpansionSupportWitness.monotone P.graph s _ _
    (P.clusters_mono (Finset.subset_insert x t))
  have he := P2MCoveredPolynomialLocality.variable_eq_nf P m hm s (axioms P K)
    (P2MCoveredRep.expOp P m s t) (P2MCoveredMonomialNormalForms.multilinear P m hm s t) x
    (fun d hd => P2MCoveredMultiplicationSupport.local_reduction P hP hml m hm overlap hoverlap s c hc hexp t hbudget d hd x)
  rw [he]
  change nf m (axioms P K) (ML (X x*nf m (axioms P J) (xMon t)))=_
  rw [P2MBooleanNormalFormMultiplication.nested_product m hm _ _ (axioms_mono P J K hJK) _ _ (xMon_multilinear t),
    AC02Frege.P2MBooleanVariableProducts.monomial_insert]
  rfl

theorem polynomial (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p)
    (hbudget : (overlap : ℝ)*((p.totalDegree : ℝ)+1) ≤ c*s/2) (x : σ) :
    P2MCoveredLinearMap.operator P m s (ML (X x*P2MCoveredLinearMap.operator P m s p))=
      P2MCoveredLinearMap.operator P m s (ML (X x*p)) := by
  classical
  let M := P2MCoveredLinearMap.operator P m s |>.comp (ML.comp (LinearMap.mulLeft (ZMod 2) (X x)))
  have he : P2MCoveredLinearMap.operator P m s p=
      ∑ d∈p.support, coeff d p • P2MCoveredRep.expOp P m s d.support := by
    have hh := congrArg (P2MCoveredLinearMap.operator P m s) p.as_sum
    rw [map_sum] at hh
    exact hh.trans (Finset.sum_congr rfl (fun d _ => P2MCoveredLinearMap.monomial P m s d _))
  have hh := congrArg M he
  rw [map_sum] at hh
  dsimp only [M,LinearMap.comp_apply,LinearMap.mulLeft_apply] at hh
  rw [hh,P2MCoveredPolynomialLocality.variable_sum P m s p hp x]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_smul_comm,map_smul,map_smul]
  have hcard : d.support.card ≤ p.totalDegree := by
    rw [←AC02Frege.P2MBooleanBasis.squarefree_sum d (hp d hd)]
    exact le_totalDegree hd
  have hcardR : (d.support.card : ℝ) ≤ p.totalDegree := by exact_mod_cast hcard
  rw [monomial P hP hml m hm overlap hoverlap s c hc hexp d.support (by nlinarith [Nat.cast_nonneg (α:=ℝ) overlap]) x]

end SemAC02.Supplement.P2MCoveredMultiplicationIdentity
end

section
-- Inlined Solutions.P2MCoveredBackgroundCompatibility

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredBackgroundCompatibility

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MCoveredLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem monomial (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (t : Finset σ) (hbudget : (overlap : ℝ)*(t.card : ℝ) ≤ c*s/2) :
    P2MCoveredLinearMap.operator P m s (nf m (axioms P ∅) (xMon t))=P2MCoveredRep.expOp P m s t := by
  let A := P.clusters t
  let J := supS P.graph s A
  let q := nf m (axioms P ∅) (xMon t)
  have hq := P2MBooleanIdealNormalForm.spec m hm (axioms P ∅) (xMon t) (xMon_multilinear t)
  have hqml : IsMultilinear q := P2MExpansionNormalFormFixed.normal_multilinear m _ _ hq.1
  have hqdeg : q.totalDegree ≤ t.card := hq.2.2.trans_eq (xMon_totalDegree t)
  have hA : (A.card : ℝ) ≤ c*s/2 := (P.clusters_card_real overlap hoverlap t).trans hbudget
  have hProps := P2MExpansionSmallSupports.properties P.graph s c hc hexp A hA
  have hs : 0 ≤ s := by
    have hz : (0 : ℝ) ≤ (overlap : ℝ)*t.card := by positivity
    nlinarith
  have hJs : (J.card : ℝ) ≤ s := by have hh := hProps.2.1.trans hProps.2.2; dsimp [J]; linarith
  have hlocal : ∀ d∈q.support, P2MCoveredRep.expOp P m s d.support=nf m (axioms P J) (xMon d.support) := by
    intro d hd
    let B := P.clusters d.support
    have hcard : d.support.card ≤ t.card := by
      rw [←squarefree_sum d (hqml d hd)]
      exact (le_totalDegree hd).trans hqdeg
    have hB : (B.card : ℝ) ≤ c*s/2 := by
      have hh := P.clusters_card_real overlap hoverlap d.support
      have hcardR : (d.support.card : ℝ) ≤ t.card := by exact_mod_cast hcard
      exact hh.trans ((mul_le_mul_of_nonneg_left hcardR (Nat.cast_nonneg overlap : (0 : ℝ) ≤ overlap)).trans hbudget)
    have hSJ : supS P.graph s B⊆J := by
      apply P2MExpansionSupportClosure.support_subset P.graph s c hc hexp A B hA hB
      intro v hv hactive
      obtain ⟨x,hx,hvx⟩ := (P2MCoveredRep.mem_clusters P d.support v).mp hv
      obtain ⟨u,hu⟩ := hactive
      have hxq : x∈q.vars := (mem_vars_iff_mem_support _).mpr ⟨d,hd,hx⟩
      rcases P2MCoveredNormalFormVariables.active_locality P hP hml m hm ∅ t x hxq v hvx u hu with ⟨u',hu',_⟩ | hinput
      · simp at hu'
      · exact Or.inl hinput
    exact (P2MCoveredNormalFormLocality.locality P hP hml m hm s c hc hexp d.support hB J hSJ hJs).symm
  rw [P2MCoveredPolynomialLocality.eq_nf P m hm s (axioms P J) q hqml hlocal]
  exact P2MBooleanNormalFormAlgebra.nested m hm (axioms P ∅) (axioms P J)
    (axioms_mono P ∅ J (Finset.empty_subset J)) (xMon t) (xMon_multilinear t)

theorem polynomial (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p)
    (hbudget : (overlap : ℝ)*(p.totalDegree : ℝ) ≤ c*s/2) :
    P2MCoveredLinearMap.operator P m s (nf m (axioms P ∅) p)=P2MCoveredLinearMap.operator P m s p := by
  classical
  rw [P2MBooleanNormalFormAlgebra.expansion m hm (axioms P ∅) p hp,map_sum]
  have he := congrArg (P2MCoveredLinearMap.operator P m s) p.as_sum
  rw [map_sum] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_smul,P2MCoveredLinearMap.monomial]
  have hcard : d.support.card ≤ p.totalDegree := by
    rw [←squarefree_sum d (hp d hd)]
    exact le_totalDegree hd
  have hcardR : (d.support.card : ℝ) ≤ p.totalDegree := by exact_mod_cast hcard
  rw [monomial P hP hml m hm overlap hoverlap s c hc hexp d.support ((mul_le_mul_of_nonneg_left hcardR (Nat.cast_nonneg overlap : (0 : ℝ) ≤ overlap)).trans hbudget)]

end SemAC02.Supplement.P2MCoveredBackgroundCompatibility
end

section
-- Inlined Solutions.P2MRestrictionLeadingMonomial

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRestrictionLeadingMonomial

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MBooleanNormalFormRestrictions

variable {σ : Type} [DecidableEq σ]

lemma filtered_indicator_le (e : σ →₀ ℕ) (he : ∀ x, e x ≤ 1) (keep : σ → Prop) [DecidablePred keep] :
    Finsupp.indicator (e.support.filter keep) (fun _ _ => 1) ≤ e := by
  intro x
  by_cases hx : x∈e.support.filter keep
  · have hs := (Finset.mem_filter.mp hx).1
    have hp := Finsupp.mem_support_iff.mp hs
    simp only [Finsupp.indicator_apply,dif_pos hx]
    omega
  · simp only [Finsupp.indicator_apply,dif_neg hx]
    exact Nat.zero_le _

lemma coeff_zero (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2)
    (d e : σ →₀ ℕ) (he : ∀ x, e x ≤ 1) (hnot : ¬ d ≤ e) (a : ZMod 2) :
    coeff d (restrict keep α (MvPolynomial.monomial e a))=0 := by
  rw [squarefree_monomial e a he,map_smul,P2MBooleanNormalFormRestrictions.monomial,xMon_eq_monomial]
  rw [smul_smul,smul_monomial]
  rw [MvPolynomial.coeff_monomial]
  split_ifs with hd
  · exfalso
    apply hnot
    rw [←hd]
    exact filtered_indicator_le e he keep
  · rfl

lemma monomial_fixed (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2)
    (e : σ →₀ ℕ) (he : ∀ x, e x ≤ 1) (hkeep : ∀ x∈e.support, keep x) (a : ZMod 2) :
    restrict keep α (MvPolynomial.monomial e a)=MvPolynomial.monomial e a := by
  rw [squarefree_monomial e a he,map_smul,P2MBooleanNormalFormRestrictions.monomial]
  have hfilter : e.support.filter keep=e.support := Finset.filter_eq_self.mpr hkeep
  have hnone : e.support.filter (fun x => ¬ keep x)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (Finset.mem_filter.mp hx).2 (hkeep x (Finset.mem_filter.mp hx).1)
  rw [hnone,Finset.prod_empty,one_smul,hfilter]

theorem coeff_leading (m : MonomialOrder σ) (keep : σ → Prop) [DecidablePred keep]
    (α : σ → ZMod 2) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (hn : p≠0)
    (hkeep : ∀ x∈(m.degree p).support, keep x) :
    coeff (m.degree p) (restrict keep α p)=coeff (m.degree p) p := by
  classical
  have hsum : restrict keep α p=∑ e∈p.support, restrict keep α (MvPolynomial.monomial e (coeff e p)) := by
    simpa only [map_sum] using congrArg (restrict keep α) p.as_sum
  rw [hsum,coeff_sum]
  rw [Finset.sum_eq_single (m.degree p)]
  · rw [monomial_fixed keep α (m.degree p) (hp _ (m.degree_mem_support hn)) hkeep]
    simp [coeff_monomial]
  · intro e he hne
    apply coeff_zero keep α (m.degree p) e (hp e he)
    intro hle
    have heq : m.degree p=e := m.toSyn.injective (le_antisymm (m.toSyn_monotone hle) (m.le_degree he))
    exact hne heq.symm
  · intro hnot
    exact (hnot (m.degree_mem_support hn)).elim

theorem nonzero (m : MonomialOrder σ) (keep : σ → Prop) [DecidablePred keep]
    (α : σ → ZMod 2) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (hn : p≠0)
    (hkeep : ∀ x∈(m.degree p).support, keep x) : restrict keep α p≠0 := by
  intro hz
  have hcoeff := coeff_leading m keep α p hp hn hkeep
  rw [hz,MvPolynomial.coeff_zero] at hcoeff
  exact (m.coeff_degree_ne_zero_iff.mpr hn) hcoeff.symm

end SemAC02.Supplement.P2MRestrictionLeadingMonomial
end

section
-- Inlined Solutions.P2MCoveredAxiomSupport

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredAxiomSupport

open MvPolynomial AC02Frege AC02Frege.P2MBooleanBasis

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [DecidableEq R]

theorem leading_covers (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p ∈ P.axioms, IsMultilinear p) (m : MonomialOrder σ)
    (u : L) (p : MvPolynomial σ (ZMod 2)) (hp : p ∈ P.Fu u) (hn : p ≠ 0)
    (v : R) (huv : P.graph.Adj u v) : v ∈ P.clusters (m.degree p).support := by
  obtain ⟨α, hFu, hF0⟩ := P2MCoveredPolynomialAssignment.assignment P hP hml {u} v u (by simp [huv])
  have hpml : IsMultilinear p := hml p (Or.inr ⟨u, hp⟩)
  by_contra hnot
  have hkeep : ∀ x ∈ (m.degree p).support, v ∉ P.cover x := by
    intro x hx he
    exact hnot ((P2MCoveredRep.mem_clusters P _ v).mpr ⟨x, hx, he⟩)
  have hpin := P2MRestrictionLeadingMonomial.nonzero m (fun x => v ∉ P.cover x) α p hpml hn hkeep
  have hz := hFu p hp
  rw [P2MCoveredRestrictionBasics.as_restriction] at hz
  exact hpin hz

theorem witness (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p ∈ P.axioms, IsMultilinear p) (m : MonomialOrder σ)
    (u : L) (p : MvPolynomial σ (ZMod 2)) (hp : p ∈ P.Fu u) (hn : p ≠ 0) :
    ∃ t : Finset σ, t.card ≤ p.totalDegree ∧
      (∀ v, P.graph.Adj u v → v ∈ P.clusters t) ∧
      (∀ x ∈ p.vars, ∀ v ∈ P.cover x, v ∈ P.clusters t) := by
  have hpml : IsMultilinear p := hml p (Or.inr ⟨u, hp⟩)
  refine ⟨(m.degree p).support, ?_, leading_covers P hP hml m u p hp hn, ?_⟩
  · rw [← squarefree_sum (m.degree p) (hpml _ (m.degree_mem_support hn))]
    exact le_totalDegree (m.degree_mem_support hn)
  · intro x hx v hv
    exact leading_covers P hP hml m u p hp hn v ⟨p, hp, x, hx, hv⟩

end SemAC02.Supplement.P2MCoveredAxiomSupport
end

section
-- Inlined Solutions.P2MCoveredAxiomAnnihilation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCoveredAxiomAnnihilation

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MCoveredLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem left_axiom (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (u : L) (p : MvPolynomial σ (ZMod 2)) (hp : p∈P.Fu u)
    (hbudget : (overlap : ℝ)*(p.totalDegree : ℝ) ≤ c*s/2) : P2MCoveredLinearMap.operator P m s p=0 := by
  by_cases hn : p=0
  · rw [hn,map_zero]
  obtain ⟨t,ht,hneighbors,hvars⟩ := P2MCoveredAxiomSupport.witness P hP hml m u p hp hn
  let A := P.clusters t
  let J := supS P.graph s A
  have hA : (A.card : ℝ) ≤ c*s/2 := by
    have htR : (t.card : ℝ) ≤ p.totalDegree := by exact_mod_cast ht
    exact (P.clusters_card_real overlap hoverlap t).trans
      ((mul_le_mul_of_nonneg_left htR (Nat.cast_nonneg overlap : (0 : ℝ) ≤ overlap)).trans hbudget)
  have hProps := P2MExpansionSmallSupports.properties P.graph s c hc hexp A hA
  have hJs : (J.card : ℝ) ≤ s := by have hh := hProps.2.1.trans hProps.2.2; dsimp [J]; linarith
  have hu : u∈J := by
    apply P2MExpansionSupportWitness.contains P.graph s A {u} (by simpa using hs) _ (Finset.mem_singleton_self u)
    intro v hv
    have hfilter : ({u} : Finset L).filter (fun a => P.graph.Adj a v)≠∅ := by
      intro he
      have hh := (Finset.mem_filter.mp hv).2
      rw [he,Finset.card_empty] at hh
      omega
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hfilter
    have hau : a=u := Finset.mem_singleton.mp (Finset.mem_filter.mp ha).1
    exact hneighbors v (hau ▸ (Finset.mem_filter.mp ha).2)
  have hpml : IsMultilinear p := hml p (Or.inr ⟨u,hp⟩)
  have hlocal : ∀ d∈p.support, P2MCoveredRep.expOp P m s d.support=nf m (axioms P J) (xMon d.support) := by
    intro d hd
    have hBsub : P.clusters d.support⊆A := by
      rintro v hv
      obtain ⟨x,hx,hvx⟩ := (P2MCoveredRep.mem_clusters P d.support v).mp hv
      exact hvars x ((mem_vars_iff_mem_support _).mpr ⟨d,hd,hx⟩) v hvx
    have hB : ((P.clusters d.support).card : ℝ) ≤ c*s/2 := by
      have hh : ((P.clusters d.support).card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hBsub
      exact hh.trans hA
    exact (P2MCoveredNormalFormLocality.locality P hP hml m hm s c hc hexp d.support hB J
      (P2MExpansionSupportWitness.monotone P.graph s _ A hBsub) hJs).symm
  rw [P2MCoveredPolynomialLocality.eq_nf P m hm s (axioms P J) p hpml hlocal]
  exact P2MBooleanNormalFormAlgebra.of_ideal m hm (axioms P J) p hpml
    (Ideal.subset_span (Or.inl (Or.inr ⟨u,hu,hp⟩)))

theorem background_axiom (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (p : MvPolynomial σ (ZMod 2)) (hp : p∈P.F0)
    (hbudget : (overlap : ℝ)*(p.totalDegree : ℝ) ≤ c*s/2) : P2MCoveredLinearMap.operator P m s p=0 := by
  have hpml : IsMultilinear p := hml p (Or.inl hp)
  rw [←P2MCoveredBackgroundCompatibility.polynomial P hP hml m hm overlap hoverlap s c hc hexp p hpml hbudget,
    P2MBooleanNormalFormAlgebra.of_ideal m hm (axioms P ∅) p hpml
      (Ideal.subset_span (Or.inl (Or.inl hp))),map_zero]

end SemAC02.Supplement.P2MCoveredAxiomAnnihilation
end

section
-- Inlined Solutions.P2MBackgroundNormalFormOne

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBackgroundNormalFormOne

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

theorem irreducible {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (hzero : ∃ y : σ → Bool, ∀ g∈G, eval (toF2 y) g=0) : IsIrred m G ∅ := by
  obtain ⟨y,hy⟩ := hzero
  have hvanish : Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ≤ RingHom.ker (eval (toF2 y)) := by
    apply Ideal.span_le.mpr
    intro p hp
    change eval (toF2 y) p=0
    rcases hp with hp | ⟨i,rfl⟩
    · exact hy p hp
    · cases hi : y i <;> simp [map_sub,map_pow,toF2,hi]
  intro q hq hn he
  have hdeg : m.degree q=0 := by simpa [xMon] using he
  have hconst := m.degree_eq_zero_iff.mp hdeg
  have hc := AC02Frege.P2MLinearStandardMonomials.leadingCoeff_one m hn
  have hqzero : eval (toF2 y) q=0 := hvanish hq.2
  rw [hconst,hc,eval_C] at hqzero
  exact one_ne_zero hqzero

theorem fixed {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (hzero : ∃ y : σ → Bool, ∀ g∈G, eval (toF2 y) g=0) : nf m G 1=1 := by
  simpa only [xMon,Finset.prod_empty] using P2MExpansionNormalFormFixed.nf_fixed m G ∅ (irreducible m G hzero)

end SemAC02.Supplement.P2MBackgroundNormalFormOne
end

section
-- Inlined Solutions.P2MPseudoReductionSoundness

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPseudoReductionSoundness

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces

theorem multilinear_lines {V : Type} (F : Set (MvPolynomial V (ZMod 2)))
    (π : List (MvPolynomial V (ZMod 2))) (hπ : PCNonBool.IsDerivation ML F π) :
    ∀ p∈π, IsMultilinear p := by
  have hz : ∀ k (hk : k<π.length), ML π[k]=π[k] := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ k hk with ⟨f,hf,a,he⟩ | ⟨i,j,hi,hj,a,b,he⟩ | ⟨i,hi,v,he⟩
      · rw [he,map_smul,ml_of_multilinear _ (ml_multilinear _)]
      · rw [he,map_add,map_smul,map_smul,ih i hi (hi.trans hk),ih j hj (hj.trans hk)]
      · rw [he,ml_of_multilinear _ (ml_multilinear _)]
  intro p hp
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hp
  rw [←hz k hk]
  exact ml_multilinear _

theorem derivation {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial V (ZMod 2))) (R : Ble V B →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (hF : ∀ f∈F, f∈Ble V B) (π : List (MvPolynomial V (ZMod 2)))
    (hπ : PCNonBool.IsDerivation ML F π) (hBle : ∀ p∈π, p∈Ble V B) :
    ∀ p (hp : p∈π), R ⟨p,hBle p hp⟩=0 := by
  have hz : ∀ k (hk : k<π.length), R ⟨π[k],hBle _ (List.getElem_mem hk)⟩=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ k hk with ⟨f,hf,a,he⟩ | ⟨i,j,hi,hj,a,b,he⟩ | ⟨i,hi,v,he⟩
      · have hml := ((mem_Ble_iff B f).mp (hF f hf)).1
        have he' : (⟨π[k],hBle _ (List.getElem_mem hk)⟩ : Ble V B)=a • ⟨f,hF f hf⟩ := by
          apply Subtype.ext
          simpa only [Submodule.coe_smul,ml_of_multilinear f hml] using he
        rw [he',map_smul,hR.1 f hf (hF f hf),smul_zero]
      · have he' : (⟨π[k],hBle _ (List.getElem_mem hk)⟩ : Ble V B)=
            a • ⟨π[i],hBle _ (List.getElem_mem (hi.trans hk))⟩+
            b • ⟨π[j],hBle _ (List.getElem_mem (hj.trans hk))⟩ := Subtype.ext he
        rw [he',map_add,map_smul,map_smul,ih i hi (hi.trans hk),ih j hj (hj.trans hk)]
        simp
      · have hb : ML (X v*π[i])∈Ble V B := by rw [←he]; exact hBle _ (List.getElem_mem hk)
        have hh := hR.2 ⟨π[i],hBle _ (List.getElem_mem (hi.trans hk))⟩ v hb (ih i hi (hi.trans hk))
        have he' : (⟨π[k],hBle _ (List.getElem_mem hk)⟩ : Ble V B)=⟨ML (X v*π[i]),hb⟩ := Subtype.ext he
        rwa [he']
  intro p hp
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact hz k hk

end SemAC02.Supplement.P2MPseudoReductionSoundness
end

section
-- Inlined Solutions.P2MCoveredPseudoReduction

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MCoveredPseudoReduction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

noncomputable def reduction (P : P2MCoveredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (K : ℕ) :
    Ble σ K →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  (P2MCoveredLinearMap.operator P m s).comp (Ble σ K).subtype

theorem pseudo (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p ∈ P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (K : ℕ) (hK : (overlap : ℝ)*((K : ℝ)+1) ≤ c*s/2) :
    IsPseudoRed P.axioms (reduction P m s K) := by
  have hOverlap : (0 : ℝ) ≤ overlap := Nat.cast_nonneg _
  constructor
  · intro p hp hpK
    have hdeg := ((P2MBooleanDegreeSpaces.mem_Ble_iff K p).mp hpK).2
    have hbudget : (overlap : ℝ)*(p.totalDegree : ℝ) ≤ c*s/2 := by
      have hh : (p.totalDegree : ℝ) ≤ K := by exact_mod_cast hdeg
      nlinarith
    rcases hp with hp | ⟨u, hp⟩
    · exact P2MCoveredAxiomAnnihilation.background_axiom P hP hml m hm overlap hoverlap s c hc hexp p hp hbudget
    · exact P2MCoveredAxiomAnnihilation.left_axiom P hP hml m hm overlap hoverlap s c hs hc hexp u p hp hbudget
  · intro p x hx hz
    have hp := (P2MBooleanDegreeSpaces.mem_Ble_iff K (p : MvPolynomial σ (ZMod 2))).mp p.2
    have hbudget : (overlap : ℝ)*(((p : MvPolynomial σ (ZMod 2)).totalDegree : ℝ)+1) ≤ c*s/2 := by
      have hh : (((p : MvPolynomial σ (ZMod 2)).totalDegree : ℝ)) ≤ K := by exact_mod_cast hp.2
      nlinarith
    change P2MCoveredLinearMap.operator P m s (ML (X x*(p : MvPolynomial σ (ZMod 2)))) = 0
    change P2MCoveredLinearMap.operator P m s (p : MvPolynomial σ (ZMod 2)) = 0 at hz
    rw [← P2MCoveredMultiplicationIdentity.polynomial P hP hml m hm overlap hoverlap s c hc hexp _ hp.1 hbudget x,
      hz, mul_zero, map_zero, map_zero]

theorem sup_empty (P : P2MCoveredRep σ L R) (s c : ℝ) (hs : 0 ≤ s) (hc : 0 < c)
    (hexp : IsBdryExp P.graph s c) : supS P.graph s ∅ = ∅ := by
  have hbudget : ((∅ : Finset R).card : ℝ) ≤ c*s/2 := by simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hh := (P2MExpansionSmallSupports.properties P.graph s c hc hexp ∅ hbudget).2.1
  have hz : (supS P.graph s ∅).card = 0 := by
    simp only [Finset.card_empty, Nat.cast_zero, zero_div] at hh
    exact_mod_cast (le_antisymm hh (Nat.cast_nonneg (α:=ℝ) _))
  exact Finset.card_eq_zero.mp hz

theorem one (P : P2MCoveredRep σ L R) (m : MonomialOrder σ)
    (hzero : ∃ y : σ → Bool, ∀ g ∈ P.F0, eval (toF2 y) g = 0)
    (s c : ℝ) (hs : 0 ≤ s) (hc : 0 < c) (hexp : IsBdryExp P.graph s c) :
    P2MCoveredLinearMap.operator P m s 1 = 1 := by
  have he : (1 : MvPolynomial σ (ZMod 2)) = xMon ∅ := by simp [AC02Frege.xMon]
  rw [he, P2MCoveredLinearMap.xMon]
  change nf m (P.axiomsOn (supS P.graph s (P.clusters ∅))) (xMon ∅) = 1
  have hcl : P.clusters ∅ = ∅ := by simp [P2MCoveredRep.clusters]
  have hA : P.axiomsOn ∅ = P.F0 := by ext p; simp [P2MCoveredRep.axiomsOn]
  rw [hcl, sup_empty P s c hs hc hexp, hA,
    P2MExpansionNormalFormFixed.nf_fixed m P.F0 ∅ (P2MBackgroundNormalFormOne.irreducible m P.F0 hzero)]
  simp [AC02Frege.xMon]

theorem no_refutation (P : P2MCoveredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p ∈ P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (overlap : ℕ) (hoverlap : ∀ x, (P.cover x).card ≤ overlap)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (K : ℕ) (hK : (overlap : ℝ)*((K : ℝ)+1) ≤ c*s/2)
    (hdegree : ∀ p ∈ P.axioms, p.totalDegree ≤ K)
    (hzero : ∃ y : σ → Bool, ∀ g ∈ P.F0, eval (toF2 y) g = 0)
    (π : List (MvPolynomial σ (ZMod 2))) (hπ : PCNonBool.IsDerivation ML P.axioms π)
    (hπdegree : ∀ p ∈ π, p.totalDegree ≤ K) : (1 : MvPolynomial σ (ZMod 2)) ∉ π := by
  intro hOne
  have hF : ∀ p ∈ P.axioms, p ∈ Ble σ K := fun p hp =>
    (P2MBooleanDegreeSpaces.mem_Ble_iff K p).mpr ⟨hml p hp, hdegree p hp⟩
  have hBle : ∀ p ∈ π, p ∈ Ble σ K := fun p hp =>
    (P2MBooleanDegreeSpaces.mem_Ble_iff K p).mpr
      ⟨P2MPseudoReductionSoundness.multilinear_lines P.axioms π hπ p hp, hπdegree p hp⟩
  have hz := P2MPseudoReductionSoundness.derivation P.axioms (reduction P m s K)
    (pseudo P hP hml m hm overlap hoverlap s c hs hc hexp K hK) hF π hπ hBle 1 hOne
  change P2MCoveredLinearMap.operator P m s 1 = 0 at hz
  rw [one P m hzero s c (by linarith) hc hexp] at hz
  exact one_ne_zero hz

end SemAC02.Supplement.P2MCoveredPseudoReduction
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
-- Inlined Solutions.P2MFunctionalPHPDegreeBound

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPDegreeBound

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MFunctionalPHPCoveredRepresentation

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem normalized_axiom (G : PCNonBool.BipGraph L R) (p : MvPolynomial (Edge G) (ZMod 2))
    (hp : p ∈ fphpG G) : ML p ∈ (representation G).axioms := by
  classical
  rcases hp with ⟨u, rfl⟩ | ⟨u, v, v', h, h', hne, rfl⟩ | ⟨u, u', v, h, h', hne, rfl⟩
  · right
    refine ⟨u, ?_⟩
    change ML _ ∈ {P2MCNFExpansionPolynomials.polynomial (rowClause G u)}
    rw [Set.mem_singleton_iff, P2MCNFExpansionPolynomials.polynomial, raw_row]
    simp only [CharTwo.sub_eq_add]
  · let e : Edge G := ⟨(u, v), h⟩
    let f : Edge G := ⟨(u, v'), h'⟩
    have hconflict : Conflict e f := by
      refine ⟨?_, Or.inl rfl⟩
      intro he
      exact hne (congrArg (fun e : Edge G => e.val.2) he)
    have hbg : xE G u v h*xE G u v' h' ∈ background G := ⟨e, f, hconflict, rfl⟩
    left
    rwa [ml_of_multilinear _ (background_multilinear G _ hbg)]
  · let e : Edge G := ⟨(u, v), h⟩
    let f : Edge G := ⟨(u', v), h'⟩
    have hconflict : Conflict e f := by
      refine ⟨?_, Or.inr rfl⟩
      intro he
      exact hne (congrArg (fun e : Edge G => e.val.1) he)
    have hbg : xE G u v h*xE G u' v h' ∈ background G := ⟨e, f, hconflict, rfl⟩
    left
    rwa [ml_of_multilinear _ (background_multilinear G _ hbg)]

theorem derivation (G : PCNonBool.BipGraph L R) (π : List (MvPolynomial (Edge G) (ZMod 2)))
    (hπ : PCNonBool.IsDerivation ML (fphpG G) π) :
    PCNonBool.IsDerivation ML (representation G).axioms π := by
  intro k hk
  rcases hπ k hk with ⟨p, hp, a, he⟩ | hcomb | hmul
  · left
    exact ⟨ML p, normalized_axiom G p hp, a, by simpa only [ml_of_multilinear _ (ml_multilinear p)] using he⟩
  · exact Or.inr (Or.inl hcomb)
  · exact Or.inr (Or.inr hmul)

theorem no_refutation (G : PCNonBool.BipGraph L R) (m : MonomialOrder (Edge G))
    (hm : IsDegCompatible m) (d K : ℕ)
    (hdegree : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ d) (hKdegree : max 2 d ≤ K)
    (s ε : ℝ) (hs : 1 ≤ s) (hε : 0 < ε) (hExp : IsBdryExp G s ε)
    (hbudget : (d : ℝ)*((K : ℝ)+1) ≤ ε*s/2)
    (π : List (MvPolynomial (Edge G) (ZMod 2))) (hπ : PCNonBool.IsDerivation ML (fphpG G) π)
    (hπdegree : ∀ p ∈ π, p.totalDegree ≤ K) : (1 : MvPolynomial (Edge G) (ZMod 2)) ∉ π := by
  exact P2MCoveredPseudoReduction.no_refutation (representation G)
    (P2MFunctionalPHPCoveredRespectfulness.respectful G) (multilinear G) m hm
    d (overlap G d hdegree) s ε hs hε (by simpa only [graph_eq] using hExp) K hbudget
    (fun p hp => (degrees G d hdegree p hp).trans hKdegree)
    (P2MFunctionalPHPCoveredRespectfulness.background_zero G) π (derivation G π hπ) hπdegree

end SemAC02.Supplement.P2MFunctionalPHPDegreeBound
end

section
-- Inlined Solutions.P2MFunctionalPHPDegreeContradiction

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MFunctionalPHPDegreeContradiction

open MvPolynomial AC02Frege

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem not_derivable_one (G : PCNonBool.BipGraph L R) (d B : ℕ)
    (hdegree : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ d) (hBdegree : max 2 d ≤ B)
    (s ε : ℝ) (hs : 1 ≤ s) (hε : 0 < ε) (hExp : IsBdryExp G s ε)
    (hbudget : (d : ℝ)*((B : ℝ)+1) ≤ ε*s/2) :
    ¬ P2MRelativePCFinite.Derivable (fphpG G) (Ble (Edge G) B) 1 := by
  classical
  letI : LinearOrder (Edge G) := LinearOrder.lift' (Fintype.equivFin (Edge G)) (Fintype.equivFin (Edge G)).injective
  letI : WellFoundedGT (Edge G) := ⟨Finite.wellFounded_of_trans_of_irrefl _⟩
  rintro (hz | ⟨π, hπ, hmem, hOne⟩)
  · exact one_ne_zero hz
  · exact P2MFunctionalPHPDegreeBound.no_refutation G MonomialOrder.degLex P2MDegreeLexCompatibility.compatible
      d B hdegree hBdegree s ε hs hε hExp hbudget π hπ
      (fun p hp => ((P2MBooleanDegreeSpaces.mem_Ble_iff B p).mp (hmem p hp)).2) hOne

end SemAC02.Supplement.P2MFunctionalPHPDegreeContradiction
end

section
-- Inlined Solutions.P2MFunctionalPHPCompatibleSeparation

set_option maxHeartbeats 3500000

namespace SemAC02.Supplement.P2MFunctionalPHPCompatibleSeparation

open MvPolynomial AC02Frege AC02Frege.P2MBooleanBasis P2MFunctionalPHPMatchingVariables
open P2MFunctionalPHPCompatibleSets P2MFunctionalPHPCompatibleRestriction P2MProofComplexity

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def Eligible (G : PCNonBool.BipGraph L R) (μ : R → L) (k : ℕ) (S : Finset (Free G μ)) : Prop :=
  ∃ A : Finset (Selected G μ), Compatible G μ A ∧ A.card ≤ k ∧ A.map (freeEmbedding G μ) = S

noncomputable def space (G : PCNonBool.BipGraph L R) (μ : R → L) (k : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Free G μ) (ZMod 2)) := monomialSpan (Eligible G μ k)

theorem separation (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (d B k : ℕ) (hdegree : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ d)
    (hB : max 2 d+2*d ≤ B) (s δ : ℝ) (hs : 1 ≤ s) (hδ : 2 < δ)
    (hExp : IsBdryExp (addMatching G μ) s δ)
    (hbudget : (d : ℝ)*((B : ℝ)+1) ≤ (δ-2)*s/2)
    (p : MvPolynomial (Free G μ) (ZMod 2)) (hp : p ∈ space G μ k)
    (hderive : P2MRelativePCFinite.Derivable (P2MFunctionalPHPAffineSubstitution.sigma G μ '' fphpG (addMatching G μ))
      (Ble (Free G μ) B) p) : p = 0 := by
  classical
  by_contra hnonzero
  obtain ⟨hml, hsupport⟩ := (mem_monomialSpan_iff (Eligible G μ k) p).mp hp
  obtain ⟨a, ha, hmax⟩ := p.support.exists_max_image (fun e => e.support.card) (support_nonempty.mpr hnonzero)
  obtain ⟨A, hA, hAk, himage⟩ := hsupport a ha
  let H := addMatching G μ
  let HA := P2MBipartiteInducedSubgraph.graph H (rows G μ A) (holes G μ A)
  have hOriginal := P2MFunctionalPHPMatchingDerivation.derivable G μ hμ d B hdegree hB p hderive
  have hB' : max 2 d ≤ B := (Nat.le_add_right (max 2 d) (2*d)).trans hB
  let label := P2MFunctionalPHPRestrictionExtraction.supportLabel G μ A a.support himage
  have hRestricted (β : a.support → Bool) : P2MRelativePCFinite.Derivable (fphpG HA) (Ble (Edge HA) B)
      (P2MRelativePCRestriction.transport (restriction G μ A (β ∘ label))
        (P2MRelativePCRenaming.transport Subtype.val p)) := by
    exact P2MFPHPPartialMatchingRestriction.derivable H (rows G μ A) (holes G μ A)
      (choice G μ A (β ∘ label)) (choice_injective G μ A hA _) (choice_mem G μ A _)
      (choice_edge G μ A _) d B hdegree hB' _ hOriginal
  have hSum := P2MLocalBooleanConsequence.relative_sum (fphpG HA) (Ble (Edge HA) B) Finset.univ
    (fun β : a.support → Bool => P2MRelativePCRestriction.transport (restriction G μ A (β ∘ label))
      (P2MRelativePCRenaming.transport Subtype.val p)) (fun β _ => hRestricted β)
  have hOne := P2MFunctionalPHPRestrictionExtraction.extraction G μ p hml a ha hmax A hA himage
  change (∑ β : a.support → Bool, P2MRelativePCRestriction.transport (restriction G μ A (β ∘ label))
    (P2MRelativePCRenaming.transport Subtype.val p)) = 1 at hOne
  rw [hOne] at hSum
  exact P2MFunctionalPHPDegreeContradiction.not_derivable_one HA d B
    (P2MBipartiteDeletionExpansion.left_degree H (rows G μ A) (holes G μ A) d hdegree) hB'
    s (δ-2) hs (by linarith) (P2MFunctionalPHPCompatibleSets.expansion G μ A hA s δ hExp) hbudget hSum

end SemAC02.Supplement.P2MFunctionalPHPCompatibleSeparation
end

section
-- Inlined Solutions.P2MRelativePC

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
    Derivable P U (c • p) := by
  rcases hp with rfl | ⟨π,hπ,hmem,hp⟩
  · simp only [smul_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; left
    exact ⟨i,i,hi,hi,c,0,by simp only [hpi,zero_smul,add_zero]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmem q hq
    · have he : q = c • p := List.mem_singleton.mp hq
      rw [he]
      exact U.smul_mem c (hmem p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p q : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
    Derivable P U (p+q) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ,hρ,hρmem,hq⟩
  · simpa only [add_zero] using (show Derivable P U p from Or.inr ⟨π,hπ,hπmem,hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j,hj,hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p+q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i,j,hi,hj,1,1,by simp only [hpi,hqj,one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπmem r hr
      · exact hρmem r hr
    · have he : r = p+q := List.mem_singleton.mp hr
      rw [he]
      exact U.add_mem (hπmem p hp) (hρmem q hq)

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (v : Fin n)
    (hmem : ML (X v * p) ∈ U) : Derivable P U (ML (X v * p)) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simp only [mul_zero,map_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i,hi,v,by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπmem q hq
    · rwa [List.mem_singleton.mp hq]

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.RelativePCPolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

theorem pc_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : Derivable P U u) (huml : IsMultilinear u)
    (hmem : ∀ w : MvPolynomial (Fin n) (ZMod 2), w.totalDegree ≤ v.totalDegree → ML (u*w) ∈ U) :
    Derivable P U (ML (u*v)) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    have he : u * C c = c • u := by rw [smul_eq_C_mul, mul_comm]
    rw [he, map_smul, ml_of_multilinear u huml]
    exact pc_smul P U hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add, map_add]
    exact pc_add P U (ihm (fun w hw => hmem w (hw.trans hdm)))
      (ihp (fun w hw => hmem w (hw.trans hdp)))
  | mul_X p i ih =>
    have hle : p.totalDegree ≤ (p * X i).totalDegree := by
      by_cases hp : p = 0
      · simp [hp]
      · rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
    have hi := ih (fun w hw => hmem w (hw.trans hle))
    have he : ML (u * (p * X i)) = ML (X i * ML (u*p)) := by
      rw [ml_mul_right]
      congr 1
      ring
    rw [he]
    apply pc_mul_X P U hi i
    rw [← he]
    exact hmem _ le_rfl

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.SemanticMonomialLocality

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates
open SemAC02.P2MProductCoordinates SemAC02.P2MCoordinateSpaces SemAC02.P2MBooleanLocality

namespace SemAC02.P2MMonomialLocality

theorem eval_monomial_squarefree {V : Type} (s : V →₀ ℕ) (a : ZMod 2) (x : V → ZMod 2) :
    eval x (monomial s a) = a * eval x (xMon s.support) := by
  calc
    eval x (monomial s a) = eval x (ML (monomial s a)) := (eval_ml _ _).symm
    _ = a * eval x (xMon s.support) := by
      rw [ml_monomial, squarefree_monomial (sqfree s) a (fun i => by simp [sqfree, Finsupp.mapRange_apply]),
        sqfree_support, smul_eval]

theorem coordinate_monomial {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) =
      a • coordinateMap g hg S (xMon T.1 * xMon s.support) := by
  funext z
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * monomial s a)) =
      a • (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon s.support)) := by
    funext X
    simp only [map_mul, eval_monomial_squarefree, Pi.smul_apply, smul_eq_mul]
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (xMon T.1 * monomial s a)) S = _
  rw [he, map_smul]
  rfl

theorem support_card_le_sum {V : Type} (s : V →₀ ℕ) : s.support.card ≤ s.sum (fun _ e => e) := by
  classical
  change s.support.card ≤ ∑ i ∈ s.support, s i
  calc
    s.support.card = ∑ _i ∈ s.support, 1 := by simp
    _ ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem degreeSpace_mono {n D E : ℕ} (hDE : D ≤ E) : degreeSpace n D ≤ degreeSpace n E := by
  intro u hu
  obtain ⟨r, hr, he⟩ := (mem_degreeSpace u).mp hu
  exact (mem_degreeSpace u).mpr ⟨r, hr.trans hDE, he⟩

theorem squarefree_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ localSpace (U.image Prod.fst) := by
  exact coordinates_product_local g hg S T U

theorem squarefree_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ degreeSpace n U.card := by
  have hl := squarefree_local g hg S T U
  obtain ⟨r, hr, he⟩ := represents_local_function (U.image Prod.fst)
    (coordinateMap g hg S (xMon T.1 * xMon U)) hl
  exact (mem_degreeSpace _).mpr ⟨r, hr.trans (Finset.card_image_le), he⟩

theorem monomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ localSpace (s.support.image Prod.fst) := by
  rw [coordinate_monomial]
  exact Submodule.smul_mem _ a (squarefree_local g hg S T s.support)

theorem monomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ degreeSpace n (s.sum (fun _ e => e)) := by
  rw [coordinate_monomial]
  apply Submodule.smul_mem
  exact degreeSpace_mono (support_card_le_sum s) (squarefree_degree g hg S T s.support)

end SemAC02.P2MMonomialLocality
end

section
-- Inlined Solutions.SemanticCoefficientControl

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates
open SemAC02.P2MCoordinateSpaces SemAC02.P2MMonomialLocality

namespace SemAC02.P2MCoefficientControl

theorem coordinate_polynomial_sum {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (f p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (f * p) = ∑ s ∈ p.support,
      coordinateMap g hg S (f * monomial s (p.coeff s)) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum, map_sum]

theorem basis_polynomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (xMon T.1 * p) ∈ degreeSpace n p.totalDegree := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  exact degreeSpace_mono (le_totalDegree hs) (monomial_degree g hg S T s (p.coeff s))

theorem basis_polynomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) :
    coordinateMap g hg S (xMon T.1 * p) ∈ localSpace J := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  have hsub : s.support.image Prod.fst ⊆ J := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact hp v ((support_subset_vars_of_mem_support hs) hv)
  exact localSpace_mono hsub (monomial_local g hg S T s (p.coeff s))

theorem coefficient_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ degreeSpace n p.totalDegree := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (degreeSpace n p.totalDegree).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_degree g hg S ⟨T, hT⟩ p
  exact hle hf

theorem coefficient_locality {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ localSpace J := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (localSpace J).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_local g hg S ⟨T, hT⟩ p J hp
  exact hle hf

end SemAC02.P2MCoefficientControl
end

section
-- Inlined Solutions.SemanticCoefficientPolynomials

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip
open SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates SemAC02.P2MCoordinateSpaces
open SemAC02.P2MBooleanFunctionPolynomials SemAC02.P2MCoefficientControl

namespace SemAC02.P2MCoefficientPolynomials

noncomputable def coefficientMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  (polynomialMap n).comp (coordinateMap g hg S)

theorem coefficient_multilinear {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    IsMultilinear (coefficientMap g hg S p) := polynomial_multilinear _

@[simp] theorem eval_coefficient {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) :
    eval (toF2 z) (coefficientMap g hg S p) = coordinates g hg p S z := eval_polynomial _ _

theorem coefficient_congr {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p q : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (he : ∀ X : Fin n × Fin m → Bool, eval (toF2 X) p = eval (toF2 X) q) :
    coefficientMap g hg S p = coefficientMap g hg S q := by
  apply multilinear_ext_bool (coefficient_multilinear g hg S p) (coefficient_multilinear g hg S q)
  intro z
  simp only [eval_coefficient, coordinates]
  exact congrArg (fun u => (fibreBasis g hg z).equivFun u S)
    (funext (fun X : Fibre g z => he X.1))

@[simp] theorem coefficient_ml {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coefficientMap g hg S (ML p) = coefficientMap g hg S p :=
  coefficient_congr g hg S _ _ (fun _ => eval_ml _ _)

theorem coefficient_degree_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    (coefficientMap g hg S (f * p)).totalDegree ≤ p.totalDegree :=
  polynomial_degree _ (coefficient_degree g hg f hf p S)

theorem ble_degree {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) (hp : p ∈ Ble V D) :
    p.totalDegree ≤ D := by
  classical
  have hle : Ble V D ≤ restrictTotalDegree V (ZMod 2) D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    exact (mem_restrictTotalDegree V D _).mpr ((xMon_totalDegree A).trans_le hA)
  exact (mem_restrictTotalDegree V D p).mp (hle hp)

theorem coefficient_degree_multSpace {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (D : ℕ) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hp : p ∈ multSpace f D)
    (S : GlobalIndex g n) : (coefficientMap g hg S p).totalDegree ≤ D := by
  obtain ⟨q, hq, rfl⟩ := hp
  change (coefficientMap g hg S (ML (f * q))).totalDegree ≤ D
  rw [coefficient_ml]
  exact (coefficient_degree_product g hg f hf q S).trans (ble_degree D q hq)

theorem coordinates_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p * v) S z = ∑ T : GlobalIndex g n,
      coordinates g hg p T z * coordinates g hg (xMon T.1 * v) S z := by
  classical
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p * v)) =
      ∑ T : GlobalIndex g n, coordinates g hg p T z •
        (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * v)) := by
    funext X
    simp only [map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [coordinates_expansion g hg p z X, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (p * v)) S = _
  rw [he, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinates]

theorem coefficient_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coefficientMap g hg S (p * v) = ∑ T : GlobalIndex g n,
      ML (coefficientMap g hg T p * coefficientMap g hg S (xMon T.1 * v)) := by
  classical
  refine multilinear_ext_bool (coefficient_multilinear g hg S _) ?_ ?_
  · exact (mem_restrictDegree (Fin n) _ 1).mp
      (Submodule.sum_mem _ (fun _ _ => (mem_restrictDegree (Fin n) _ 1).mpr (ml_multilinear _)))
  · intro z
    simp only [eval_coefficient, map_sum, eval_ml, map_mul]
    exact coordinates_mul g hg p v S z

end SemAC02.P2MCoefficientPolynomials
end

section
-- Inlined Solutions.P2MRelativeSpaceAlgebra

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MRelativeSpaceAlgebra

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
  rw [he, mem_light_iff]

theorem mem_multSpace_of_degree {V : Type} [Finite V]
    (f Q : MvPolynomial V (ZMod 2)) (D : ℕ) (hQ : Q.totalDegree ≤ D) :
    mulML f Q ∈ multSpace f D := by
  refine ⟨ML Q, (mem_Ble_iff D _).mpr ⟨ml_multilinear _, (ml_totalDegree_le _).trans hQ⟩, ?_⟩
  change ML (f * ML Q) = ML (f * Q)
  exact ml_mul_right f Q

theorem multSpace_multilinear {V : Type} (f p : MvPolynomial V (ZMod 2)) (D : ℕ)
    (hp : p ∈ multSpace f D) : IsMultilinear p := by
  obtain ⟨Q,_,rfl⟩ := hp
  exact ml_multilinear _

theorem multSpace_degree {V : Type} (f p : MvPolynomial V (ZMod 2)) (k D : ℕ)
    (hf : f ∈ Ble V k) (hp : p ∈ multSpace f D) : p.totalDegree ≤ k+D := by
  obtain ⟨Q,hQ,rfl⟩ := hp
  change (ML (f*Q)).totalDegree ≤ k+D
  exact (ml_totalDegree_le _).trans ((totalDegree_mul f Q).trans
    (Nat.add_le_add ((mem_Ble_iff k f).mp hf).2 ((mem_Ble_iff D Q).mp hQ).2))

theorem relative_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (f Q v : MvPolynomial (Fin n) (ZMod 2)) (D : ℕ)
    (hp : P2MRelativePC.Derivable P (multSpace f D) (mulML f Q))
    (hdeg : Q.totalDegree + v.totalDegree ≤ D) :
    P2MRelativePC.Derivable P (multSpace f D) (ML (mulML f Q * v)) := by
  apply P2MRelativePC.pc_polynomial_mul P (multSpace f D) (mulML f Q) v hp (ml_multilinear _)
  intro w hw
  have he : ML (mulML f Q * w) = mulML f (Q*w) := by
    change ML (ML (f*Q) * w) = ML (f*(Q*w))
    rw [ml_mul_left, mul_assoc]
  rw [he]
  apply mem_multSpace_of_degree
  exact (totalDegree_mul Q w).trans (by omega)

end SemAC02.P2MRelativeSpaceAlgebra
end

section
-- Inlined Solutions.P2MBooleanDimension

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanDimension

abbrev DegreeIndex (n D : ℕ) := {A : Finset (Fin n) // A.card ≤ D}

theorem span_degree_monomials (n D : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun A : DegreeIndex n D => xMon A.1)) = Ble (Fin n) D := by
  congr 1
  ext p
  constructor
  · rintro ⟨A,rfl⟩
    exact ⟨A.1,A.2,rfl⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨⟨A,hA⟩,rfl⟩

noncomputable def degreeBasis (n D : ℕ) : Basis (DegreeIndex n D) (ZMod 2) (Ble (Fin n) D) :=
  (Basis.span (xMon_linearIndependent.comp (fun A : DegreeIndex n D => A.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree_monomials n D))

instance finite_Ble (n D : ℕ) : Module.Finite (ZMod 2) (Ble (Fin n) D) :=
  Module.Finite.of_basis (degreeBasis n D)

def degreeIndexEquiv (n D : ℕ) : DegreeIndex n D ≃
    (j : Fin (min D n + 1)) × {A : Finset (Fin n) // A.card = j.1} where
  toFun A := ⟨⟨A.1.card, by
    have hcard := Finset.card_le_univ A.1
    simp only [Fintype.card_fin] at hcard
    omega⟩,A.1,rfl⟩
  invFun B := ⟨B.2.1,by have := B.1.2; have := B.2.2; omega⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv B := by
    rcases B with ⟨⟨j,hj⟩,A,hA⟩
    cases hA
    rfl

theorem finrank_Ble (n D : ℕ) : finrank (ZMod 2) (Ble (Fin n) D) = Hn n D := by
  classical
  rw [Module.finrank_eq_card_basis (degreeBasis n D), Fintype.card_congr (degreeIndexEquiv n D), Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range _ _

theorem Hn_pos (n D : ℕ) : 0 < Hn n D := by
  unfold Hn
  apply lt_of_lt_of_le (show 0 < n.choose 0 by simp)
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

end SemAC02.P2MBooleanDimension
end

section
-- Inlined Solutions.P2MMultiplierSupportCount

set_option maxHeartbeats 1000000

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MMultiplierSupportCount

abbrev MultiplierIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :=
  {S : Finset (Fin n × Fin m) // S.card ≤ k ∧ IsLnSupport g S}

theorem multiplier_span {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun S : MultiplierIndex g n k => xMon S.1)) =
      multiplierSpace g n k := by
  unfold multiplierSpace
  congr 1
  ext p
  constructor
  · rintro ⟨S,rfl⟩
    exact ⟨S.1,S.2,rfl⟩
  · rintro ⟨S,hS,rfl⟩
    exact ⟨⟨S,hS⟩,rfl⟩

noncomputable def multiplierBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Basis (MultiplierIndex g n k) (ZMod 2) (multiplierSpace g n k) :=
  (Basis.span (xMon_linearIndependent.comp (fun S : MultiplierIndex g n k => S.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (multiplier_span g n k))

instance finite_multiplierSpace {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Module.Finite (ZMod 2) (multiplierSpace g n k) := Module.Finite.of_basis (multiplierBasis g n k)

theorem finrank_multiplier {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    finrank (ZMod 2) (multiplierSpace g n k) =
      (Finset.univ.filter (fun S : Finset (Fin n × Fin m) => S.card ≤ k ∧ IsLnSupport g S)).card := by
  rw [Module.finrank_eq_card_basis (multiplierBasis g n k)]
  exact Fintype.card_subtype _

abbrev LowIndex (V : Type) (k : ℕ) := {S : Finset V // S.card ≤ k}

def lowIndexEquiv (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    LowIndex V k ≃ (j : Fin (min k (Fintype.card V)+1)) × {S : Finset V // S.card = j.1} where
  toFun S := ⟨⟨S.1.card,by have := Finset.card_le_univ S.1; omega⟩,S.1,rfl⟩
  invFun T := ⟨T.2.1,by have := T.1.2; have := T.2.2; omega⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv T := by rcases T with ⟨⟨j,hj⟩,S,hS⟩; cases hS; rfl

theorem low_support_card (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).card = Hn (Fintype.card V) k := by
  rw [← Fintype.card_subtype,Fintype.card_congr (lowIndexEquiv V k),Fintype.card_sigma]
  simp only [Fintype.card_finset_len]
  exact Fin.sum_univ_eq_sum_range _ _

end SemAC02.P2MMultiplierSupportCount
end

section
-- Inlined Solutions.P2MBooleanDegreeBasis

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanDegreeBasis

abbrev DegreeIndex (V : Type) (K : ℕ) := {T : Finset V // T.card ≤ K}

theorem degree_span (V : Type) (K : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun T : DegreeIndex V K => xMon T.1)) = Ble V K := by
  unfold Ble
  congr 1
  ext p
  constructor
  · rintro ⟨T,rfl⟩; exact ⟨T.1,T.2,rfl⟩
  · rintro ⟨T,hT,rfl⟩; exact ⟨⟨T,hT⟩,rfl⟩

noncomputable def degreeBasis (V : Type) (K : ℕ) : Basis (DegreeIndex V K) (ZMod 2) (Ble V K) :=
  (Basis.span (xMon_linearIndependent.comp (fun T : DegreeIndex V K => T.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (degree_span V K))

instance finite_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) : Module.Finite (ZMod 2) (Ble V K) :=
  Module.Finite.of_basis (degreeBasis V K)

theorem finrank_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) :
    finrank (ZMod 2) (Ble V K) = Hn (Fintype.card V) K := by
  rw [Module.finrank_eq_card_basis (degreeBasis V K)]
  have he : Fintype.card (DegreeIndex V K) =
      (Finset.univ.filter (fun T : Finset V => T.card ≤ K)).card := Fintype.card_subtype _
  rw [he]
  exact P2MMultiplierSupportCount.low_support_card V K

end SemAC02.P2MBooleanDegreeBasis
end

section
-- Inlined Solutions.P2MNaiveBooleanReduction

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MNaiveBooleanReduction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces

variable {V : Type} [Fintype V] [DecidableEq V]

def consequences (P : Set (MvPolynomial V (ZMod 2))) (B : ℕ) :
    Submodule (ZMod 2) (MvPolynomial V (ZMod 2)) where
  carrier := {p | P2MRelativePCFinite.Derivable P (Ble V B) p}
  zero_mem' := P2MRelativePCFinite.pc_zero _ _
  add_mem' := P2MRelativePCFinite.pc_add _ _
  smul_mem' := fun a _ hp => P2MRelativePCFinite.pc_smul _ _ hp a

noncomputable def reduction (P : Set (MvPolynomial V (ZMod 2))) (B : ℕ) :
    Ble V B →ₗ[ZMod 2] (Ble V B ⧸ (consequences P B).comap (Ble V B).subtype) :=
  ((consequences P B).comap (Ble V B).subtype).mkQ

theorem zero_iff (P : Set (MvPolynomial V (ZMod 2))) (B : ℕ) (p : Ble V B) :
    reduction P B p = 0 ↔ P2MRelativePCFinite.Derivable P (Ble V B) p.val :=
  Submodule.Quotient.mk_eq_zero _

theorem pseudo (P : Set (MvPolynomial V (ZMod 2))) (B : ℕ) : IsPseudoRed P (reduction P B) := by
  constructor
  · intro p hp hpB
    apply (zero_iff P B _).mpr
    have hml := ((mem_Ble_iff B p).mp hpB).1
    have hh := P2MRelativePCFinite.pc_axiom P (Ble V B) p hp (by rwa [ml_of_multilinear p hml])
    rwa [ml_of_multilinear p hml] at hh
  · intro p v hv hz
    exact (zero_iff P B _).mpr
      (P2MRelativePCFinite.pc_mul_X P (Ble V B) ((zero_iff P B p).mp hz) v hv)

theorem rank_lower (P : Set (MvPolynomial V (ZMod 2))) (B k : ℕ) (hkB : k ≤ B)
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) (hUk : U ≤ Ble V k)
    (hsep : ∀ p ∈ U, P2MRelativePCFinite.Derivable P (Ble V B) p → p = 0) :
    Module.finrank (ZMod 2) U ≤ rankLe (reduction P B) k := by
  let R := reduction P B
  let T := (Submodule.comap (Ble V B).subtype (Ble V k)).map R
  have hUB : U ≤ Ble V B := hUk.trans (P2MPseudoReductionRestriction.ble_mono hkB)
  let f : U →ₗ[ZMod 2] T :=
    { toFun := fun p => ⟨R ⟨p.val, hUB p.property⟩, ⟨⟨p.val, hUB p.property⟩, hUk p.property, rfl⟩⟩
      map_add' := by
        intro p q
        apply Subtype.ext
        change R ⟨p.val+q.val, _⟩ = R ⟨p.val, _⟩+R ⟨q.val, _⟩
        exact map_add R ⟨p.val, hUB p.property⟩ ⟨q.val, hUB q.property⟩
      map_smul' := by
        intro a p
        apply Subtype.ext
        change R ⟨a • p.val, _⟩ = a • R ⟨p.val, _⟩
        exact map_smul R a ⟨p.val, hUB p.property⟩ }
  have hf : Function.Injective f := by
    intro p q he
    have he' : R ⟨p.val, hUB p.property⟩ = R ⟨q.val, hUB q.property⟩ := congrArg Subtype.val he
    have hz : R (⟨p.val, hUB p.property⟩-⟨q.val, hUB q.property⟩) = 0 := by rw [map_sub, he', sub_self]
    have hderive := (zero_iff P B _).mp hz
    have hdiff := hsep (p.val-q.val) (U.sub_mem p.property q.property) hderive
    exact Subtype.ext (sub_eq_zero.mp hdiff)
  exact LinearMap.finrank_le_finrank_of_injective hf

end SemAC02.Supplement.P2MNaiveBooleanReduction
end

section
-- Inlined Solutions.P2MFunctionalPHPCompatibleRank

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPCompatibleRank

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
open P2MFunctionalPHPMatchingVariables P2MFunctionalPHPCompatibleSets P2MFunctionalPHPCompatibleSeparation P2MProofComplexity

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem space_le (G : PCNonBool.BipGraph L R) (μ : R → L) (k : ℕ) : space G μ k ≤ Ble (Free G μ) k := by
  apply Submodule.span_le.mpr
  rintro p ⟨S, ⟨A, hA, hcard, himage⟩, rfl⟩
  exact (P2MBooleanDegreeSpaces.mem_Ble_iff k _).mpr ⟨xMon_multilinear S, by
    rw [xMon_totalDegree, ← himage, Finset.card_map]
    exact hcard⟩

instance finite_space (G : PCNonBool.BipGraph L R) (μ : R → L) (k : ℕ) :
    Module.Finite (ZMod 2) (space G μ k) :=
  Module.Finite.of_injective (Submodule.inclusion (space_le G μ k)) (Submodule.inclusion_injective _)

theorem count_le_dimension (G : PCNonBool.BipGraph L R) (μ : R → L) (k : ℕ) :
    (P2MSeparatedSetCounting.sets (P2MCompatibleFamilyCounting.conflicts
      (P2MCompatibleEdgeNeighborhoods.family (addMatching G μ) (reserved G μ) (hole G μ))) k).card ≤
        Module.finrank (ZMod 2) (space G μ k) := by
  classical
  let E := P2MSeparatedSetCounting.sets (P2MCompatibleFamilyCounting.conflicts
    (P2MCompatibleEdgeNeighborhoods.family (addMatching G μ) (reserved G μ) (hole G μ))) k
  have hmem (A : E) : xMon (A.val.map (freeEmbedding G μ)) ∈ space G μ k := by
    obtain ⟨hcard, hgood⟩ := (P2MSeparatedSetCounting.mem_sets _ _ _).mp A.property
    exact Submodule.subset_span ⟨_, ⟨A.val, (compatible_iff_good G μ A.val).mpr hgood, hcard.le, rfl⟩, rfl⟩
  let b (A : E) : space G μ k := ⟨xMon (A.val.map (freeEmbedding G μ)), hmem A⟩
  have hb : LinearIndependent (ZMod 2) b := by
    apply LinearIndependent.of_comp (space G μ k).subtype
    apply xMon_linearIndependent.comp
    intro A B he
    apply Subtype.ext
    exact Finset.map_injective (freeEmbedding G μ) he
  simpa only [Fintype.card_coe] using hb.fintype_card_le_finrank

theorem power_dimension (G : PCNonBool.BipGraph L R) (μ : R → L) (dL dR k : ℕ)
    (hL : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ dL)
    (hR : ∀ v, P2MCleaningDegreeReduction.rightDegree (addMatching G μ) v ≤ dR) :
    (Fintype.card (Selected G μ)-(2*dR*dL*(dR+dL))*(k-1))^k ≤
      k.factorial*Module.finrank (ZMod 2) (space G μ k) :=
  (P2MFunctionalPHPCompatibleSets.count G μ dL dR hL hR k).trans
    (Nat.mul_le_mul_left _ (count_le_dimension G μ k))

theorem rank (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (dL dR B k : ℕ) (hdegree : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ dL)
    (hR : ∀ v, P2MCleaningDegreeReduction.rightDegree (addMatching G μ) v ≤ dR)
    (hB : max 2 dL+2*dL ≤ B) (hkB : k ≤ B) (s δ : ℝ) (hs : 1 ≤ s) (hδ : 2 < δ)
    (hExp : IsBdryExp (addMatching G μ) s δ)
    (hbudget : (dL : ℝ)*((B : ℝ)+1) ≤ (δ-2)*s/2) :
    (Fintype.card (Selected G μ)-(2*dR*dL*(dR+dL))*(k-1))^k ≤
      k.factorial*rankLe
        (P2MNaiveBooleanReduction.reduction (P2MFunctionalPHPAffineSubstitution.sigma G μ '' fphpG (addMatching G μ)) B) k := by
  have hRank := P2MNaiveBooleanReduction.rank_lower _ B k hkB (space G μ k) (space_le G μ k)
    (separation G μ hμ dL B k hdegree hB s δ hs hδ hExp hbudget)
  exact (power_dimension G μ dL dR k hdegree hR).trans (Nat.mul_le_mul_left _ hRank)

end SemAC02.Supplement.P2MFunctionalPHPCompatibleRank
end

section
-- Inlined Solutions.P2MBooleanVariableEquivalence

set_option maxHeartbeats 2000000

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanVariableEquivalence

theorem multilinear_rename {V W : Type} (e : V ≃ W) {p : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) : IsMultilinear (rename e p) := by
  classical
  intro s hs w
  rw [support_rename_of_injective e.injective] at hs
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
  simpa only [Finsupp.mapDomain_equiv_apply] using hp t ht (e.symm w)

theorem ml_rename {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (p : MvPolynomial V (ZMod 2)) : rename e (ML p) = ML (rename e p) := by
  apply multilinear_ext (multilinear_rename e (ml_multilinear p)) (ml_multilinear _)
  intro x
  simp only [eval_rename,eval_ml]

theorem rename_mem_Ble {V W : Type} (e : V ≃ W) {k : ℕ} {p : MvPolynomial V (ZMod 2)}
    (hp : p ∈ Ble V k) : rename e p ∈ Ble W k := by
  rcases P2MBooleanDegreeSpaces.mem_Ble_iff k p |>.mp hp with ⟨hml,hdeg⟩
  exact (P2MBooleanDegreeSpaces.mem_Ble_iff k _).mpr
    ⟨multilinear_rename e hml,(totalDegree_rename_le e p).trans hdeg⟩

theorem map_Ble {V W : Type} (e : V ≃ W) (k : ℕ) :
    (Ble V k).map (rename e).toLinearMap = Ble W k := by
  apply le_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact rename_mem_Ble e hp
  · intro p hp
    refine ⟨rename e.symm p,rename_mem_Ble e.symm hp,?_⟩
    exact (renameEquiv (ZMod 2) e).apply_symm_apply p

theorem mulML_rename {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f p : MvPolynomial V (ZMod 2)) : rename e (mulML f p) = mulML (rename e f) (rename e p) := by
  simp only [mulML,LinearMap.comp_apply,LinearMap.mulLeft_apply]
  rw [ml_rename,map_mul]

theorem rename_mem_multSpace {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) {p : MvPolynomial V (ZMod 2)}
    (hp : p ∈ multSpace f k) : rename e p ∈ multSpace (rename e f) k := by
  obtain ⟨q,hq,rfl⟩ := hp
  exact ⟨rename e q,rename_mem_Ble e hq,(mulML_rename e f q).symm⟩

theorem map_multSpace {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) :
    (multSpace f k).map (rename e).toLinearMap = multSpace (rename e f) k := by
  apply le_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact rename_mem_multSpace e f k hp
  · intro p hp
    have hf : rename e.symm (rename e f) = f := (renameEquiv (ZMod 2) e).symm_apply_apply f
    refine ⟨rename e.symm p,?_,?_⟩
    · have hh := rename_mem_multSpace e.symm (rename e f) k hp
      rw [hf] at hh
      exact hh
    · exact (renameEquiv (ZMod 2) e).apply_symm_apply p

theorem finrank_map {V W : Type} (e : V ≃ W)
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) :
    Module.finrank (ZMod 2) (U.map (rename e).toLinearMap) = Module.finrank (ZMod 2) U := by
  exact (Submodule.equivMapOfInjective (rename e).toLinearMap
    (renameEquiv (ZMod 2) e).injective U).finrank_eq.symm

noncomputable def spaceEquiv {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) :
    multSpace f k ≃ₗ[ZMod 2] multSpace (rename e f) k where
  toFun u := ⟨rename e u.val,rename_mem_multSpace e f k u.property⟩
  invFun u := ⟨rename e.symm u.val,by
    have h := rename_mem_multSpace e.symm (rename e f) k u.property
    have hf : rename e.symm (rename e f) = f := (renameEquiv (ZMod 2) e).symm_apply_apply f
    rw [hf] at h
    exact h⟩
  left_inv u := Subtype.ext ((renameEquiv (ZMod 2) e).symm_apply_apply u.val)
  right_inv u := Subtype.ext ((renameEquiv (ZMod 2) e).apply_symm_apply u.val)
  map_add' u v := Subtype.ext (map_add (rename e) u.val v.val)
  map_smul' a u := Subtype.ext ((rename e).toLinearMap.map_smul a u.val)

@[simp] theorem spaceEquiv_val {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) (u : multSpace f k) :
    (spaceEquiv e f k u).val = rename e u.val := rfl

@[simp] theorem spaceEquiv_symm_val {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) (u : multSpace (rename e f) k) :
    ((spaceEquiv e f k).symm u).val = rename e.symm u.val := rfl

end SemAC02.P2MBooleanVariableEquivalence
end

section
-- Inlined Solutions.P2MBooleanPseudoReductionEquivalence

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MBooleanPseudoReductionEquivalence

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanVariableEquivalence

variable {V U W : Type} [Finite V] [Finite U] [AddCommGroup W] [Module (ZMod 2) W]

noncomputable def degreeEquiv (e : V ≃ U) (B : ℕ) : Ble V B ≃ₗ[ZMod 2] Ble U B where
  toFun p := ⟨rename e p.val, rename_mem_Ble e p.property⟩
  invFun p := ⟨rename e.symm p.val, rename_mem_Ble e.symm p.property⟩
  left_inv p := Subtype.ext ((renameEquiv (ZMod 2) e).symm_apply_apply p.val)
  right_inv p := Subtype.ext ((renameEquiv (ZMod 2) e).apply_symm_apply p.val)
  map_add' p q := Subtype.ext (map_add (rename e) p.val q.val)
  map_smul' a p := Subtype.ext ((rename e).toLinearMap.map_smul a p.val)

noncomputable def reduction (e : V ≃ U) {B : ℕ} (R : Ble V B →ₗ[ZMod 2] W) : Ble U B →ₗ[ZMod 2] W :=
  R.comp (degreeEquiv e B).symm.toLinearMap

theorem pseudo (e : V ≃ U) {B : ℕ} (F : Set (MvPolynomial V (ZMod 2)))
    (R : Ble V B →ₗ[ZMod 2] W) (hR : IsPseudoRed F R) :
    IsPseudoRed (rename e '' F) (reduction e R) := by
  constructor
  · rintro p ⟨q, hq, rfl⟩ hp
    have he : rename e.symm (rename e q) = q := (renameEquiv (ZMod 2) e).symm_apply_apply q
    have hqB := rename_mem_Ble e.symm hp
    rw [he] at hqB
    have hval : (degreeEquiv e B).symm ⟨rename e q, hp⟩ = ⟨q, hqB⟩ := Subtype.ext he
    change R ((degreeEquiv e B).symm _) = 0
    rw [hval]
    exact hR.1 q hq hqB
  · intro p v hmem hz
    have he : rename e.symm (ML (X v*p.val)) = ML (X (e.symm v)*rename e.symm p.val) := by
      rw [ml_rename, map_mul, rename_X]
    have hmem' := rename_mem_Ble e.symm hmem
    rw [he] at hmem'
    have hh := hR.2 ((degreeEquiv e B).symm p) (e.symm v) hmem' hz
    change R ((degreeEquiv e B).symm _) = 0
    convert hh using 1
    exact congrArg R (Subtype.ext he)

theorem rank_eq (e : V ≃ U) {B : ℕ} (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) :
    rankLe (reduction e R) k = rankLe R k := by
  have heq : (Submodule.comap (Ble U B).subtype (Ble U k)).map (reduction e R) =
      (Submodule.comap (Ble V B).subtype (Ble V k)).map R := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(degreeEquiv e B).symm p, rename_mem_Ble e.symm hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨degreeEquiv e B p, rename_mem_Ble e hp, ?_⟩
      change R ((degreeEquiv e B).symm (degreeEquiv e B p)) = R p
      rw [LinearEquiv.symm_apply_apply]
  unfold rankLe
  rw [heq]

end SemAC02.Supplement.P2MBooleanPseudoReductionEquivalence
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
-- Inlined Solutions.P2MSPSFiniteSizeBound

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MSPSFiniteSizeBound

open MvPolynomial ACirc AC02Frege AC02Frege.P2MBooleanAlgebra

variable {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem refutation (f : V → U) (F : Set (MvPolynomial V (ZMod 2)))
    (π : List (ACirc (ZMod 2) V)) (hπ : IsSemPCRef IsSPS Set.univ (polyAx F) π) :
    IsSemPCRef IsSPS Set.univ (polyAx (rename f '' F))
      (π.map (P2MArithmeticLeafSubstitution.circuit (fun v => Sum.inl (f v)))) := by
  apply P2MSemanticLeafSubstitution.refutation (fun v => Sum.inl (f v)) _ _ _ _
    (P2MArithmeticLeafSubstitution.sps _) _ π hπ
  rintro a ⟨p, hp, rfl⟩
  left
  refine ⟨polyFn (rename f p), ⟨rename f p, ⟨p, hp, rfl⟩, rfl⟩, ?_⟩
  intro y
  simp only [polyFn, eval_rename]
  rfl

theorem lower (F : Set (MvPolynomial V (ZMod 2))) (d₀ : ℕ)
    (hF : ∀ f ∈ F, IsMultilinear f ∧ f.totalDegree ≤ d₀)
    (k r : ℕ) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) (hr : 1 ≤ r) (hrn : r ≤ Fintype.card V)
    (hB : 3*(k+max d₀ r) ≤ Fintype.card V)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V (3*(k+max d₀ r)) →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (π : List (ACirc (ZMod 2) V)) (hπ : IsSemPCRef IsSPS Set.univ (polyAx F) π) :
    (rankLe R k : ℝ)/(2*((Fintype.card V-r).choose k : ℝ)) ≤ topS Set.univ π := by
  let e := Fintype.equivFin V
  let R' := P2MBooleanPseudoReductionEquivalence.reduction e R
  let π' := π.map (P2MArithmeticLeafSubstitution.circuit (fun v => Sum.inl (e v)))
  have hF' : ∀ p ∈ rename e '' F, IsMultilinear p ∧ p.totalDegree ≤ d₀ := by
    rintro p ⟨q, hq, rfl⟩
    exact ⟨P2MBooleanVariableEquivalence.multilinear_rename e (hF q hq).1,
      (totalDegree_rename_le e q).trans (hF q hq).2⟩
  have hh := theorem_4_4_sps_size_bound (rename e '' F) d₀ hF' k r hk hkn hr hrn hB R'
    (P2MBooleanPseudoReductionEquivalence.pseudo e F R hR) π' (refutation e F π hπ)
  rw [P2MBooleanPseudoReductionEquivalence.rank_eq] at hh
  exact hh.trans (by exact_mod_cast P2MArithmeticLeafSubstitution.top_bound (fun v => Sum.inl (e v)) π)

end SemAC02.Supplement.P2MSPSFiniteSizeBound
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
-- Inlined Solutions.P2MShiftedCompatibleRankRatio

set_option maxHeartbeats 2500000

namespace SemAC02.Supplement.P2MShiftedCompatibleRankRatio

theorem lower (n b t k : ℕ) (hk : 1 ≤ k) (hbudget : 3*(k+((b+1)*k+t)) ≤ n)
    (rank : ℝ) (hrank : ((n : ℝ)-t-(b : ℝ)*(k-1 : ℕ))^k/(k.factorial : ℝ) ≤ rank) :
    1/2*Real.exp ((k : ℝ)^2/(2*n)) ≤ rank/(2*((n-((b+1)*k+t)).choose k : ℝ)) := by
  let r := (b+1)*k+t
  have hr : r ≤ n := by dsimp [r]; omega
  have hknr : k ≤ n-r := by dsimp [r]; omega
  have hkn : k ≤ n := by omega
  have hn : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsub : ((n-r : ℕ) : ℝ) = (n : ℝ)-r := Nat.cast_sub hr
  have hrR : (r : ℝ) = ((b : ℝ)+1)*k+t := by dsimp [r]; push_cast; rfl
  have hkSub : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by rw [Nat.cast_sub hk]; norm_num
  have hbase0 : 0 ≤ ((n-r : ℕ) : ℝ)*(1+(k : ℝ)/n) := by positivity
  have hbase : ((n-r : ℕ) : ℝ)*(1+(k : ℝ)/n) ≤
      (n : ℝ)-t-(b : ℝ)*(k-1 : ℕ) := by
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
      _ ≤ ((n : ℝ)-t-(b : ℝ)*(k-1 : ℕ))^k/(k.factorial : ℝ) :=
        div_le_div_of_nonneg_right hpow hfact.le
      _ ≤ rank := hrank
  have hExp := P2MBoundedCNFRankRatio.power_exponential n k hn hkn
  have hExpComb : ((n-r).choose k : ℝ)*Real.exp ((k : ℝ)^2/(2*n)) ≤ rank :=
    (mul_le_mul_of_nonneg_left hExp (Nat.cast_nonneg _)).trans hcomb
  have hchoosePos : (0 : ℝ) < ((n-r).choose k : ℝ) := by exact_mod_cast Nat.choose_pos hknr
  change _ ≤ rank/(2*((n-r).choose k : ℝ))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*((n-r).choose k : ℝ))).mpr
  nlinarith

end SemAC02.Supplement.P2MShiftedCompatibleRankRatio
end

section
-- Inlined Solutions.P2MFunctionalPHPFiniteBound

set_option maxHeartbeats 3500000

namespace SemAC02.Supplement.P2MFunctionalPHPFiniteBound

open MvPolynomial ACirc AC02Frege AC02Frege.P2MBooleanAlgebra P2MFunctionalPHPMatchingVariables

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem lower (G : PCNonBool.BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (dL dR t k : ℕ) (hdegree : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ dL)
    (hR : ∀ v, P2MProofComplexity.P2MCleaningDegreeReduction.rightDegree (addMatching G μ) v ≤ dR)
    (ht : Fintype.card (Selected G μ)+t = Fintype.card (Free G μ)) (hk : 1 ≤ k)
    (hrd : max 2 dL ≤ (2*dR*dL*(dR+dL)+1)*k+t)
    (hbudgetN : 3*(k+((2*dR*dL*(dR+dL)+1)*k+t)) ≤ Fintype.card (Free G μ))
    (hcertificate : max 2 dL+2*dL ≤ 3*(k+((2*dR*dL*(dR+dL)+1)*k+t)))
    (s δ : ℝ) (hs : 1 ≤ s) (hδ : 2 < δ) (hExp : IsBdryExp (addMatching G μ) s δ)
    (hbudget : (dL : ℝ)*((3*(k+((2*dR*dL*(dR+dL)+1)*k+t)) : ℕ)+1) ≤ (δ-2)*s/2)
    (π : List (ACirc (ZMod 2) (Edge (addMatching G μ))))
    (hπ : IsSemPCRef IsSPS Set.univ (polyAx (fphpG (addMatching G μ))) π) :
    1/2*Real.exp ((k : ℝ)^2/(2*Fintype.card (Free G μ))) ≤ topS Set.univ π := by
  classical
  let N := Fintype.card (Free G μ)
  let C := 2*dR*dL*(dR+dL)
  let r := (C+1)*k+t
  let B := 3*(k+max (max 2 dL) r)
  let F := P2MFunctionalPHPAffineSubstitution.sigma G μ '' fphpG (addMatching G μ)
  have hB : B = 3*(k+r) := by dsimp only [B]; rw [max_eq_right hrd]
  have hkB : k ≤ B := by dsimp [B]; omega
  have hBN : B ≤ N := by rw [hB]; exact hbudgetN
  have hF : ∀ q ∈ F, IsMultilinear q ∧ q.totalDegree ≤ max 2 dL := by
    rintro q ⟨p, hp, rfl⟩
    exact ⟨ml_multilinear _, (P2MFunctionalPHPAffineSubstitution.degree_le G μ p).trans
      (P2MFunctionalPHPRowSemantics.all_degree _ dL hdegree p hp)⟩
  let R := P2MNaiveBooleanReduction.reduction F B
  have hRank := P2MFunctionalPHPCompatibleRank.rank G μ hμ dL dR B k hdegree hR
    (by rw [hB]; exact hcertificate) hkB s δ hs hδ hExp (by rw [hB]; exact hbudget)
  have hMbound : C*(k-1) ≤ Fintype.card (Selected G μ) := by
    have hh := Nat.mul_le_mul_left C (Nat.sub_le k 1)
    change 3*(k+((C+1)*k+t)) ≤ N at hbudgetN
    change Fintype.card (Selected G μ)+t = N at ht
    nlinarith
  have hsub : ((Fintype.card (Selected G μ)-C*(k-1) : ℕ) : ℝ) =
      (N : ℝ)-t-(C : ℝ)*(k-1 : ℕ) := by
    rw [Nat.cast_sub hMbound, Nat.cast_mul]
    have hh : (Fintype.card (Selected G μ) : ℝ)+t = N := by exact_mod_cast ht
    linarith
  have hRankR : ((Fintype.card (Selected G μ)-C*(k-1) : ℕ) : ℝ)^k ≤
      (k.factorial : ℝ)*(rankLe R k : ℝ) := by exact_mod_cast hRank
  rw [hsub] at hRankR
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hRankDiv : ((N : ℝ)-t-(C : ℝ)*(k-1 : ℕ))^k/(k.factorial : ℝ) ≤ rankLe R k := by
    apply (div_le_iff₀ hfact).mpr
    nlinarith
  let π' := π.map (P2MSPSAffineSubstitution.line (P2MFunctionalPHPAffineSubstitution.terms G μ))
  obtain ⟨hπ', hTop⟩ := P2MFunctionalPHPAffineSubstitution.refutation G μ π hπ
  have h44 := P2MSPSFiniteSizeBound.lower F (max 2 dL) hF k r hk (hkB.trans hBN)
    (by dsimp [r]; omega) (by dsimp [r] at *; omega) hBN R (P2MNaiveBooleanReduction.pseudo F B) π' hπ'
  have hRatio := P2MShiftedCompatibleRankRatio.lower N C t k hk hbudgetN (rankLe R k) hRankDiv
  exact (hRatio.trans h44).trans (by exact_mod_cast hTop)

end SemAC02.Supplement.P2MFunctionalPHPFiniteBound
end

section
-- Inlined Solutions.P2MFunctionalPHPCardinality

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MFunctionalPHPCardinality

open P2MFunctionalPHPMatchingVariables P2MFunctionalPHPCoveredRepresentation

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem edge_card (G : PCNonBool.BipGraph L R) :
    Fintype.card (Edge G) = ∑ u, (PCNonBool.nbrOn G Finset.univ u).card := by
  classical
  let e : Edge G ≃ (Σ u : L, {v : R // G.Adj u v}) :=
    { toFun := fun e => ⟨e.val.1, ⟨e.val.2, e.property⟩⟩
      invFun := fun e => ⟨(e.1, e.2.val), e.2.property⟩
      left_inv := fun e => Subtype.ext rfl
      right_inv := by rintro ⟨u, v⟩; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Fintype.card_subtype]
  rfl

theorem min_degree (G : PCNonBool.BipGraph L R) (s δ : ℝ) (hs : 1 ≤ s) (hδ : 2 < δ)
    (hExp : IsBdryExp G s δ) (u : L) : 3 ≤ (PCNonBool.nbrOn G Finset.univ u).card := by
  have he : PCNonBool.boundaryOn G Finset.univ {u} = PCNonBool.nbrOn G Finset.univ u := by
    ext v
    simp only [PCNonBool.boundaryOn, PCNonBool.nbrOn, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hc
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (({u} : Finset L).filter (fun w => G.Adj w v)).card)
      have hw' := Finset.mem_filter.mp hw
      have hwu := Finset.mem_singleton.mp hw'.1
      exact hwu ▸ hw'.2
    · intro h
      have hf : (({u} : Finset L).filter (fun w => G.Adj w v)) = {u} :=
        Finset.filter_eq_self.mpr (fun w hw => by rwa [Finset.mem_singleton.mp hw])
      rw [hf, Finset.card_singleton]
  have hh := hExp {u} (by simpa only [Finset.card_singleton, Nat.cast_one] using hs)
  rw [he] at hh
  simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hh
  have hlt : (2 : ℝ) < (PCNonBool.nbrOn G Finset.univ u).card := hδ.trans_le hh
  have hltN : 2 < (PCNonBool.nbrOn G Finset.univ u).card := by exact_mod_cast hlt
  omega

theorem free_bounds {n : ℕ} (G : PCNonBool.BipGraph (Fin (n+1)) (Fin n)) (μ : Fin n → Fin (n+1))
    (d : ℕ) (hd : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ d)
    (hn : 1 ≤ n) (s δ : ℝ) (hs : 1 ≤ s) (hδ : 2 < δ) (hExp : IsBdryExp (addMatching G μ) s δ) :
    2*n ≤ Fintype.card (Free G μ) ∧ Fintype.card (Free G μ) ≤ 2*d*n := by
  have hcount := free_card G μ
  simp only [Fintype.card_fin] at hcount
  have hlow : 3*(n+1) ≤ Fintype.card (Edge (addMatching G μ)) := by
    rw [edge_card]
    have hh := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (Fin (n+1)))) =>
      min_degree (addMatching G μ) s δ hs hδ hExp u)
    simpa [Nat.mul_comm] using hh
  have hupp : Fintype.card (Edge (addMatching G μ)) ≤ d*(n+1) := by
    rw [edge_card]
    have hh := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (Fin (n+1)))) => hd u)
    simpa [Nat.mul_comm] using hh
  constructor <;> nlinarith

theorem selected_count {n : ℕ} (G : PCNonBool.BipGraph (Fin (n+1)) (Fin n))
    (μ : Fin n → Fin (n+1)) (hμ : Function.Injective μ) (d : ℕ)
    (hd : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ d) :
    ∃ t : ℕ, t ≤ d ∧ Fintype.card (Selected G μ)+t = Fintype.card (Free G μ) := by
  classical
  obtain ⟨star, hstar⟩ := unmatched μ hμ
  have hstar0 : ¬ ∃ v, μ v = star := by rw [← hstar star]; simp
  let es : Selected G μ ≃ {e : Free G μ // e.val.val.1 ≠ star} :=
    { toFun := fun e => ⟨⟨e.val, e.property.1⟩, (hstar e.val.val.1).mpr e.property.2⟩
      invFun := fun e => ⟨e.val.val, ⟨e.val.property, (hstar e.val.val.val.1).mp e.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let er : {e : Free G μ // e.val.val.1 = star} ≃ {v : Fin n // (addMatching G μ).Adj star v} :=
    { toFun := fun e => ⟨e.val.val.val.2, by simpa only [e.property] using e.val.val.property⟩
      invFun := fun v => ⟨⟨⟨(star, v.val), v.property⟩, fun h => hstar0 ⟨v.val, h.symm⟩⟩, rfl⟩
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        exact Subtype.ext (Prod.ext e.property.symm rfl)
      right_inv := by intro v; exact Subtype.ext rfl }
  have hsCard := Fintype.card_congr es
  have hrCard : Fintype.card {e : Free G μ // e.val.val.1 = star} =
      (PCNonBool.nbrOn (addMatching G μ) Finset.univ star).card := by
    rw [Fintype.card_congr er, Fintype.card_subtype]
    rfl
  refine ⟨(PCNonBool.nbrOn (addMatching G μ) Finset.univ star).card, hd star, ?_⟩
  have hc := Fintype.card_subtype_compl (fun e : Free G μ => e.val.val.1 = star)
  have hle := Fintype.card_subtype_le (fun e : Free G μ => e.val.val.1 = star)
  change Fintype.card {e : Free G μ // e.val.val.1 ≠ star} = _ at hc
  rw [← hsCard, hrCard] at hc
  rw [hrCard] at hle
  omega

end SemAC02.Supplement.P2MFunctionalPHPCardinality
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
-- Inlined Solutions.P2MFunctionalPHPLinearParameters

set_option maxHeartbeats 3500000

namespace SemAC02.Supplement.P2MFunctionalPHPLinearParameters

noncomputable def fraction (d C : ℕ) (ε γ : ℝ) : ℝ :=
  min (1/(100*((C : ℝ)+2))) (ε*γ/(100*d*((C : ℝ)+2)))

theorem fraction_pos (d C : ℕ) (ε γ : ℝ) (hd : 0 < d) (hε : 0 < ε) (hγ : 0 < γ) :
    0 < fraction d C ε γ := by
  unfold fraction
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

noncomputable def degree (d C : ℕ) (ε γ : ℝ) (n : ℕ) : ℕ := ⌊fraction d C ε γ*n⌋₊

theorem budgets (d C n N t : ℕ) (ε γ : ℝ) (hd : 0 < d) (hε : 0 < ε) (hγ : 0 < γ)
    (ht : t ≤ d) (hN : 2*n ≤ N) (hn : (100*(d+1) : ℕ) ≤ (n : ℝ))
    (hεn : (100*d*(d+1) : ℕ) ≤ ε*γ*n)
    (hηn : (8*d+4 : ℕ) ≤ fraction d C ε γ*n) :
    1 ≤ degree d C ε γ n ∧
    max 2 d ≤ (C+1)*degree d C ε γ n+t ∧
    max 2 d+2*d ≤ 3*(degree d C ε γ n+((C+1)*degree d C ε γ n+t)) ∧
    3*(degree d C ε γ n+((C+1)*degree d C ε γ n+t)) ≤ N ∧
    (d : ℝ)*((3*(degree d C ε γ n+((C+1)*degree d C ε γ n+t)) : ℕ)+1) ≤ ε*γ*n/2 ∧
    fraction d C ε γ*n/2 ≤ degree d C ε γ n := by
  let η := fraction d C ε γ
  let k := degree d C ε γ n
  have hη : 0 < η := fraction_pos d C ε γ hd hε hγ
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have htR : (t : ℝ) ≤ d := by exact_mod_cast ht
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hfloor : (k : ℝ) ≤ η*n := Nat.floor_le (by positivity)
  have hceil : η*n < (k : ℝ)+1 := Nat.lt_floor_add_one _
  have hklarge : 4*d ≤ k := by
    have hh : (4 : ℝ)*d ≤ k := by push_cast at hηn; nlinarith
    exact_mod_cast hh
  have hηC : η*(100*((C : ℝ)+2)) ≤ 1 :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 100*((C : ℝ)+2))).mp (min_le_left _ _)
  have hηE : η*(100*d*((C : ℝ)+2)) ≤ ε*γ :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 100*d*((C : ℝ)+2))).mp (min_le_right _ _)
  have hsmallN : 3*((C : ℝ)+2)*k ≤ 3*n/100 := by
    have hf := mul_le_mul_of_nonneg_left hfloor (show (0 : ℝ) ≤ 3*((C : ℝ)+2) by positivity)
    have hh := mul_le_mul_of_nonneg_right hηC hnR
    nlinarith
  have hsmallE : (d : ℝ)*3*((C : ℝ)+2)*k ≤ 3*ε*γ*n/100 := by
    have hf := mul_le_mul_of_nonneg_left hfloor (show (0 : ℝ) ≤ (d : ℝ)*3*((C : ℝ)+2) by positivity)
    have hh := mul_le_mul_of_nonneg_right hηE hnR
    nlinarith
  have hBreal : ((3*(k+((C+1)*k+t)) : ℕ) : ℝ) = 3*((C : ℝ)+2)*k+3*t := by push_cast; ring
  have hBN : 3*(k+((C+1)*k+t)) ≤ N := by
    have hNR : (2 : ℝ)*n ≤ N := by exact_mod_cast hN
    have hh : ((3*(k+((C+1)*k+t)) : ℕ) : ℝ) ≤ N := by
      push_cast at hn
      rw [hBreal]
      nlinarith
    exact_mod_cast hh
  have hBε : (d : ℝ)*((3*(k+((C+1)*k+t)) : ℕ)+1) ≤ ε*γ*n/2 := by
    rw [hBreal]
    push_cast at hεn
    nlinarith
  refine ⟨by omega, ?_, ?_, hBN, hBε, ?_⟩
  · change max 2 d ≤ (C+1)*k+t
    have hmult : k ≤ (C+1)*k := by nlinarith
    omega
  · change max 2 d+2*d ≤ 3*(k+((C+1)*k+t))
    have hmult : k ≤ (C+1)*k := by nlinarith
    omega
  · push_cast at hηn
    linarith

theorem exponential (η : ℝ) (hη : 0 < η) (D n N k : ℕ) (hD : 0 < D)
    (hN : 1 ≤ N) (hNn : N ≤ D*n) (hk : η*n/2 ≤ k) (hlarge : (32*D : ℕ) ≤ η^2*n) :
    (2 : ℝ)^(η^2/(32*D)*n) ≤ 1/2*Real.exp ((k : ℝ)^2/(2*N)) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hDn : 1 ≤ D*n := hN.trans hNn
  have hlarge' : (32 : ℝ) ≤ (η/(D : ℝ))^2*(D*n : ℕ) := by
    push_cast at hlarge ⊢
    have he : (η/(D : ℝ))^2*((D : ℝ)*n) = η^2*n/D := by field_simp <;> ring
    rw [he]
    apply (le_div_iff₀ hDR).mpr
    exact hlarge
  have hk' : (η/(D : ℝ))*(D*n : ℕ)/2 ≤ k := by
    have he : (η/(D : ℝ))*(D*n : ℕ)/2 = η*n/2 := by push_cast; field_simp
    rwa [he]
  have hh := P2MRandomCNFLinearParameters.exponential (η/D) (by positivity) (D*n) N k hN hNn hk' hlarge'
  have he : (η/(D : ℝ))^2/32*(D*n : ℕ) = η^2/(32*D)*n := by push_cast; field_simp <;> ring
  rwa [he] at hh

end SemAC02.Supplement.P2MFunctionalPHPLinearParameters
end

section
-- Inlined Solutions.P2MMatchingAugmentationExpansion

set_option maxHeartbeats 2500000

namespace P2MProofComplexity.P2MMatchingAugmentationExpansion

open PCNonBool SemAC02.Supplement

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem left_degree (G : BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (d : ℕ) (hd : ∀ u, (nbrOn G Finset.univ u).card ≤ d) (u : L) :
    (nbrOn (addMatching G μ) Finset.univ u).card ≤ d+1 := by
  have he : nbrOn (addMatching G μ) Finset.univ u =
      nbrOn G Finset.univ u ∪ Finset.univ.filter (fun v => μ v = u) := by
    ext v
    simp only [nbrOn, addMatching]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have hf : (Finset.univ.filter (fun v => μ v = u)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    exact hμ ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)
  rw [he]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hd u) hf)

theorem right_degree (G : BipGraph L R) (μ : R → L)
    (d : ℕ) (hd : ∀ v, (Finset.univ.filter (fun u => G.Adj u v)).card ≤ d) (v : R) :
    (Finset.univ.filter (fun u => (addMatching G μ).Adj u v)).card ≤ d+1 := by
  have he : Finset.univ.filter (fun u => (addMatching G μ).Adj u v) =
      (Finset.univ.filter (fun u => G.Adj u v)) ∪ {μ v} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton, addMatching, eq_comm]
  rw [he]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hd v) (by simp))

theorem boundary_loss (G : BipGraph L R) (μ : R → L) (hμ : Function.Injective μ) (J : Finset L) :
    (boundaryOn G Finset.univ J).card ≤
      (boundaryOn (addMatching G μ) Finset.univ J).card + J.card := by
  let T := Finset.univ.filter (fun v => μ v ∈ J)
  have hT : T.card ≤ J.card := by
    have hsub : T.image μ ⊆ J := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hv).2
    rw [← Finset.card_image_of_injective T hμ]
    exact Finset.card_le_card hsub
  have hsub : boundaryOn G Finset.univ J ⊆ boundaryOn (addMatching G μ) Finset.univ J ∪ T := by
    intro v hv
    by_cases hvT : v ∈ T
    · exact Finset.mem_union_right _ hvT
    · apply Finset.mem_union_left
      have hnot : μ v ∉ J := by simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hvT
      have he : J.filter (fun u => (addMatching G μ).Adj u v) = J.filter (fun u => G.Adj u v) := by
        apply Finset.filter_congr
        intro u hu
        change (G.Adj u v ∨ μ v = u) ↔ G.Adj u v
        constructor
        · rintro (h | h)
          · exact h
          · exact (hnot (h.symm ▸ hu)).elim
        · exact Or.inl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [he]; exact (Finset.mem_filter.mp hv).2⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hT _))

theorem expansion (G : BipGraph L R) (μ : R → L) (hμ : Function.Injective μ)
    (s δ : ℝ) (hG : IsBdryExp G s δ) : IsBdryExp (addMatching G μ) s (δ-1) := by
  intro J hJs
  have hg := hG J hJs
  have hh : ((boundaryOn G Finset.univ J).card : ℝ) ≤
      ((boundaryOn (addMatching G μ) Finset.univ J).card : ℝ) + J.card := by
    exact_mod_cast boundary_loss G μ hμ J
  nlinarith

end P2MProofComplexity.P2MMatchingAugmentationExpansion
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
-- Inlined Solutions.P2MFunctionalPHPLowerBound

set_option maxHeartbeats 4000000

namespace SemAC02.Supplement.P2MFunctionalPHPLowerBound

open ACirc Filter P2MProofComplexity P2MFunctionalPHPMatchingVariables

theorem full (ΔL0 ΔR0 : ℕ) (hΔL : 0 < ΔL0) (hΔR : 0 < ΔR0)
    (δ₀ γ : ℝ) (hδ : 3 < δ₀) (hγ : 0 < γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ G : PCNonBool.BipGraph (Fin (n+1)) (Fin n),
        (∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ ΔL0) →
        (∀ v, (Finset.univ.filter (fun u => G.Adj u v)).card ≤ ΔR0) →
        IsBdryExp G (γ*n) δ₀ →
        ∀ μ : Fin n → Fin (n+1), Function.Injective μ →
        ∀ π : List (ACirc (ZMod 2) (Edge (addMatching G μ))),
          IsSemPCRef IsSPS Set.univ (polyAx (fphpG (addMatching G μ))) π →
          (2 : ℝ)^(c*n) ≤ topS Set.univ π ∧ (2 : ℝ)^(c*n) ≤ csize π := by
  let dL := ΔL0+1
  let dR := ΔR0+1
  let C := 2*dR*dL*(dR+dL)
  let ε := δ₀-3
  let η := P2MFunctionalPHPLinearParameters.fraction dL C ε γ
  let D := 2*dL
  have hdL : 0 < dL := by dsimp [dL]; omega
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hη : 0 < η := P2MFunctionalPHPLinearParameters.fraction_pos dL C ε γ hdL hε hγ
  have hD : 0 < D := by dsimp [D]; omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨η^2/(32*D), by positivity, ?_⟩
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hNlarge := hNat.eventually_ge_atTop ((100*(dL+1) : ℕ) : ℝ)
  have hSlarge := (Filter.Tendsto.const_mul_atTop hγ hNat).eventually_ge_atTop 1
  have hElarge := (Filter.Tendsto.const_mul_atTop (mul_pos hε hγ) hNat).eventually_ge_atTop
    ((100*dL*(dL+1) : ℕ) : ℝ)
  have hKlarge := (Filter.Tendsto.const_mul_atTop hη hNat).eventually_ge_atTop ((8*dL+4 : ℕ) : ℝ)
  have hExponent := (Filter.Tendsto.const_mul_atTop (sq_pos_of_pos hη) hNat).eventually_ge_atTop ((32*D : ℕ) : ℝ)
  apply Filter.eventually_atTop.mp
  filter_upwards [hNlarge, hSlarge, hElarge, hKlarge, hExponent] with n hnN hnS hnE hnK hnExp
  intro G hL hR hExp μ hμ π hπ
  have hn : 1 ≤ n := by
    have hh : (1 : ℝ) ≤ n := by push_cast at hnN; nlinarith
    exact_mod_cast hh
  have hLH : ∀ u, (PCNonBool.nbrOn (addMatching G μ) Finset.univ u).card ≤ dL :=
    P2MMatchingAugmentationExpansion.left_degree G μ hμ ΔL0 hL
  have hRH : ∀ v, P2MCleaningDegreeReduction.rightDegree (addMatching G μ) v ≤ dR :=
    P2MMatchingAugmentationExpansion.right_degree G μ ΔR0 hR
  have hHExp := P2MMatchingAugmentationExpansion.expansion G μ hμ (γ*n) δ₀ hExp
  obtain ⟨hNlow, hNupper⟩ := P2MFunctionalPHPCardinality.free_bounds G μ dL hLH hn (γ*n) (δ₀-1)
    hnS (by linarith) hHExp
  obtain ⟨t, ht, hcount⟩ := P2MFunctionalPHPCardinality.selected_count G μ hμ dL hLH
  let k := P2MFunctionalPHPLinearParameters.degree dL C ε γ n
  obtain ⟨hk, hrd, hcertificate, hbudgetN, hbudget, hkLower⟩ :=
    P2MFunctionalPHPLinearParameters.budgets dL C n (Fintype.card (Free G μ)) t ε γ hdL hε hγ
      ht hNlow hnN hnE hnK
  have hbudget' : (dL : ℝ)*((3*(k+((C+1)*k+t)) : ℕ)+1) ≤ ((δ₀-1)-2)*(γ*n)/2 := by
    convert hbudget using 1 <;> dsimp only [ε] <;> ring
  have hFinite := P2MFunctionalPHPFiniteBound.lower G μ hμ dL dR t k hLH hRH
    (by simpa only [Fintype.card_eq_nat_card] using hcount) hk hrd hbudgetN
    hcertificate (γ*n) (δ₀-1) hnS (by linarith) hHExp hbudget' π hπ
  have hNumeric := P2MFunctionalPHPLinearParameters.exponential η hη D n (Fintype.card (Free G μ)) k hD
    (by omega) hNupper hkLower hnExp
  have hFinal := hNumeric.trans hFinite
  exact ⟨hFinal, hFinal.trans (by exact_mod_cast P2MArithmeticTopSize.top_le_csize Set.univ π)⟩

end SemAC02.Supplement.P2MFunctionalPHPLowerBound
end

end P2MFunctionalPHPProof
open SemAC02.Supplement MvPolynomial ACirc Filter Topology

theorem solution (ΔL0 ΔR0 : ℕ) (hΔL : 0 < ΔL0) (hΔR : 0 < ΔR0)
    (δ₀ γ : ℝ) (hδ : 3 < δ₀) (hγ : 0 < γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ G : PCNonBool.BipGraph (Fin (n + 1)) (Fin n),
        (∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ ΔL0) →
        (∀ v, (Finset.univ.filter (fun u => G.Adj u v)).card ≤ ΔR0) →
        IsBdryExp G (γ * n) δ₀ →
        ∀ μ : Fin n → Fin (n + 1), Function.Injective μ →
        ∀ π : List (ACirc (ZMod 2) (Edge (addMatching G μ))),
          IsSemPCRef IsSPS Set.univ (polyAx (fphpG (addMatching G μ))) π →
          (2 : ℝ) ^ (c * n) ≤ topS Set.univ π ∧ (2 : ℝ) ^ (c * n) ≤ csize π  := by
  exact P2MFunctionalPHPProof.SemAC02.Supplement.P2MFunctionalPHPLowerBound.full ΔL0 ΔR0 hΔL hΔR δ₀ γ hδ hγ
