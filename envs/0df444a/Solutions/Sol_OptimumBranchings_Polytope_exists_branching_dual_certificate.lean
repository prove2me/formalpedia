-- Prove2me | solution 1 for OptimumBranchings.Polytope.exists_branching_dual_certificate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T04:57:41.301842+00:00
-- url     : https://prove2.me/submissions/b3c82075-9abb-42b5-a2c5-bf08fa4365da

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron
import Definitions.Def_OptimumBranchings_Polytope_DualCertificate

set_option autoImplicit false

namespace OptimumBranchings.Polytope.DualCertProof

open OptimumBranchings.Polytope
open scoped Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Section 1: Contraction Quotient, Parent Cycles, and Ranked Branchings -/

abbrev ContractV (C : Finset V) := Option {v : V // v ∉ C}

def contract (C : Finset V) (v : V) : ContractV C :=
  if hv : v ∈ C then none else some ⟨v, hv⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contract_none_iff (C : Finset V) (v : V) : contract C v = none ↔ v ∈ C := by
  simp [contract]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contract_some (C : Finset V) (v : {v : V // v ∉ C}) :
    contract C v = some v := by
  simp [contract, v.property]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contract_eq_some_iff (C : Finset V) (v : V) (w : {v : V // v ∉ C}) :
    contract C v = some w ↔ v = w := by
  by_cases hv : v ∈ C
  · have hn : v ≠ w := fun h => w.property (h ▸ hv)
    simp [contract, hv, hn]
  · simp only [contract, hv, dite_false, Option.some.injEq]
    exact Subtype.ext_iff

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contract_surjective (C : Finset V) (hC : C.Nonempty) :
    Function.Surjective (contract C) := by
  intro q
  cases q with
  | none =>
    obtain ⟨v, hv⟩ := hC
    exact ⟨v, (contract_none_iff C v).mpr hv⟩
  | some v => exact ⟨v, contract_some C v⟩

abbrev ContractE (G : Graph V E) (C : Finset V) :=
  {e : E // contract C (G.front e) ≠ contract C (G.rear e)}

def contractGraph (G : Graph V E) (C : Finset V) : Graph (ContractV C) (ContractE G C) where
  front e := contract C (G.front e)
  rear e := contract C (G.rear e)
  front_ne_rear e := e.property

theorem contract_card_lt (C : Finset V) (hC : 2 ≤ C.card) :
    Fintype.card (ContractV C) < Fintype.card V := by
  have hsplit := Finset.card_add_card_compl C
  have hc : Fintype.card {v : V // v ∉ C} = Cᶜ.card := by
    simpa only [Finset.mem_compl] using (Fintype.card_coe Cᶜ)
  simp only [Fintype.card_option, hc]
  omega

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contract_front_ne_rear_iff (G : Graph V E) (C : Finset V) (e : E) :
    contract C (G.front e) ≠ contract C (G.rear e) ↔
      ¬ (G.front e ∈ C ∧ G.rear e ∈ C) := by
  constructor
  · rintro h ⟨hf, hr⟩
    apply h
    rw [(contract_none_iff C _).mpr hf, (contract_none_iff C _).mpr hr]
  · intro h heq
    by_cases hf : G.front e ∈ C
    · have hnone : contract C (G.rear e) = none := heq.symm.trans ((contract_none_iff C _).mpr hf)
      exact h ⟨hf, (contract_none_iff C _).mp hnone⟩
    · have hsome : contract C (G.rear e) = some ⟨G.front e, hf⟩ :=
        heq.symm.trans (contract_some C ⟨G.front e, hf⟩)
      have hfeq : G.rear e = G.front e := (contract_eq_some_iff C _ _).mp hsome
      exact G.front_ne_rear e hfeq.symm

structure ParentCycle (p : V → V) where
  support : Finset V
  nonempty : support.Nonempty
  maps : ∀ v ∈ support, p v ∈ support
  reaches : ∀ u ∈ support, ∀ v ∈ support, ∃ k : ℕ, p^[k] u = v

noncomputable def hitRank (p : V → V) (r v : V) : ℕ :=
  if h : ∃ k : ℕ, p^[k] v = r then Nat.find h else 0

omit [Fintype V] in
theorem hitRank_decreases (p : V → V) (r v : V)
    (h : ∃ k : ℕ, p^[k] v = r) (hv : v ≠ r) :
    hitRank p r (p v) < hitRank p r v := by
  have hn : Nat.find h ≠ 0 := by
    intro he
    have hs := Nat.find_spec h
    rw [he] at hs
    exact hv hs
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hs : p^[k] (p v) = r := by
    have hs := Nat.find_spec h
    rw [hk, Function.iterate_succ_apply] at hs
    exact hs
  have hp : ∃ j : ℕ, p^[j] (p v) = r := ⟨k, hs⟩
  simp only [hitRank, dif_pos h, dif_pos hp]
  rw [hk]
  exact Nat.lt_succ_of_le (Nat.find_min' hp hs)

omit [Fintype V] [DecidableEq V] in
theorem exists_parent_cycle (p : V → V) (U : Finset V) (hne : U.Nonempty)
    (hclosed : ∀ v ∈ U, p v ∈ U) :
    ∃ C : ParentCycle p, C.support ⊆ U := by
  let F := U.powerset.filter (fun C => C.Nonempty ∧ ∀ v ∈ C, p v ∈ C)
  have hF : F.Nonempty := ⟨U, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (fun _ h => h), hne, hclosed⟩⟩
  obtain ⟨C, hCF, hmin⟩ := Finset.exists_min_image F Finset.card hF
  obtain ⟨hsub, hneC, hclosedC⟩ : C ⊆ U ∧ C.Nonempty ∧ ∀ v ∈ C, p v ∈ C := by
    simpa [F] using hCF
  refine ⟨⟨C, hneC, hclosedC, ?_⟩, hsub⟩
  intro u hu v hv
  let O := C.filter (fun w => ∃ k : ℕ, p^[k] u = w)
  have hOC : O ⊆ C := Finset.filter_subset _ _
  have hO : O.Nonempty := ⟨u, Finset.mem_filter.mpr ⟨hu, ⟨0, rfl⟩⟩⟩
  have hclosedO : ∀ w ∈ O, p w ∈ O := by
    intro w hw
    obtain ⟨hwC, k, hk⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨hclosedC w hwC, k + 1, ?_⟩
    rw [Function.iterate_succ_apply', hk]
  have hOF : O ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hOC.trans hsub, hO, hclosedO⟩
  have heq : O = C := Finset.eq_of_subset_of_card_le hOC (hmin O hOF)
  have hvO : v ∈ O := heq.symm ▸ hv
  exact (Finset.mem_filter.mp hvO).2

namespace ParentCycle

variable {p : V → V}

omit [Fintype V] [DecidableEq V] in
theorem card_ge_two (C : ParentCycle p) (h : ∀ v ∈ C.support, p v ≠ v) :
    2 ≤ C.support.card := by
  obtain ⟨v, hv⟩ := C.nonempty
  exact Finset.one_lt_card.mpr ⟨v, hv, p v, C.maps v hv, (h v hv).symm⟩

omit [Fintype V] in
theorem rank_parent_lt (C : ParentCycle p) (e : V) (he : e ∈ C.support)
    (v : V) (hv : v ∈ C.support) (hne : v ≠ e) :
    hitRank p e (p v) < hitRank p e v :=
  hitRank_decreases p e v (C.reaches v hv e he) hne

omit [Fintype V] in
theorem rank_bounded (C : ParentCycle p) (e : V) :
    ∃ K : ℕ, ∀ v ∈ C.support, hitRank p e v < K := by
  refine ⟨(∑ v ∈ C.support, hitRank p e v) + 1, ?_⟩
  intro v hv
  exact Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv)

end ParentCycle

theorem scaled_rank_lt (K a b u v : ℕ) (hab : a < b) (hu : u < K) :
    K * a + u < K * b + v := by
  have h := Nat.mul_le_mul_left K (Nat.succ_le_of_lt hab)
  nlinarith

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem branching_of_rank (G : Graph V E) (B : Finset E)
    (hhead : ∀ e ∈ B, ∀ f ∈ B, G.front e = G.front f → e = f)
    (rank : V → ℕ) (hrank : ∀ e ∈ B, rank (G.rear e) < rank (G.front e)) :
    G.IsBranching B := by
  refine ⟨?_, hhead⟩
  intro F hFB hF hregular
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image F (fun e => rank (G.front e)) hF
  have hin : F.filter (fun f => G.front f = G.front e) = {e} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hf, hfe⟩
      exact hhead f (hFB hf) e (hFB he) hfe
    · rintro rfl
      exact ⟨he, rfl⟩
  have hout : F.filter (fun f => G.rear f = G.front e) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro f hf hfe
    have hlt := hrank f (hFB hf)
    rw [hfe] at hlt
    exact (not_lt_of_ge (hmax f hf)) hlt
  have hm : G.meetCount F (G.front e) = 1 := by simp [Graph.meetCount, hin, hout]
  have hh := hregular (G.front e)
  rw [hm] at hh
  omega

/-! ### Section 2: Maximum Incoming Weight & Node-Set Load -/

noncomputable def maxIn (G : Graph V E) (c : E → ℝ) (v : V) : ℝ :=
  Finset.sup' (insert 0 ((Finset.univ.filter (fun e : E => G.front e = v)).image c))
    (Finset.insert_nonempty _ _) id

omit [Fintype V] [DecidableEq E] in
theorem maxIn_nonneg (G : Graph V E) (c : E → ℝ) (v : V) :
    0 ≤ maxIn G c v := by
  unfold maxIn
  exact Finset.le_sup' (f := id) (Finset.mem_insert_self 0 _)

omit [Fintype V] [DecidableEq E] in
theorem le_maxIn (G : Graph V E) (c : E → ℝ) {e : E} {v : V} (h : G.front e = v) :
    c e ≤ maxIn G c v := by
  unfold maxIn
  apply Finset.le_sup' (f := id)
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩, rfl⟩

omit [Fintype V] [DecidableEq E] in
theorem maxIn_le_iff (G : Graph V E) (c : E → ℝ) (v : V) (M : ℝ) :
    maxIn G c v ≤ M ↔ 0 ≤ M ∧ ∀ e : E, G.front e = v → c e ≤ M := by
  unfold maxIn
  rw [Finset.sup'_le_iff]
  constructor
  · intro h
    refine ⟨h 0 (Finset.mem_insert_self 0 _), fun e he => ?_⟩
    exact h (c e) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩, rfl⟩))
  · rintro ⟨h0, he⟩ x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h0
    · obtain ⟨e, heF, rfl⟩ := Finset.mem_image.mp hx
      exact he e (Finset.mem_filter.mp heF).2

omit [Fintype V] [DecidableEq E] in
theorem exists_eq_maxIn_of_pos (G : Graph V E) (c : E → ℝ) (v : V)
    (hpos : 0 < maxIn G c v) :
    ∃ e : E, G.front e = v ∧ c e = maxIn G c v := by
  unfold maxIn at hpos ⊢
  obtain ⟨x, hx, hxeq⟩ := Finset.exists_mem_eq_sup' (Finset.insert_nonempty 0
    ((Finset.univ.filter (fun e : E => G.front e = v)).image c)) id
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · exfalso
    dsimp [id] at hxeq
    linarith [hxeq]
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx'
    exact ⟨e, (Finset.mem_filter.mp he).2, hxeq.symm⟩

def nodeSetLoad (ySet : Finset V → ℝ) (v : V) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset V => 2 ≤ S.card ∧ v ∈ S), ySet S

/-! ### Section 3: Preimage Sets and Dual Variable Lifting -/

def preimageSet (C : Finset V) (S' : Finset (ContractV C)) : Finset V :=
  Finset.univ.filter (fun v : V => contract C v ∈ S')

omit [Fintype E] [DecidableEq E] in
theorem mem_preimageSet (C : Finset V) (S' : Finset (ContractV C)) (v : V) :
    v ∈ preimageSet C S' ↔ contract C v ∈ S' := by
  simp [preimageSet]

omit [Fintype E] [DecidableEq E] in
theorem image_preimageSet (C : Finset V) (hC : C.Nonempty) (S' : Finset (ContractV C)) :
    (preimageSet C S').image (contract C) = S' := by
  ext q
  simp only [Finset.mem_image, mem_preimageSet]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hq
    obtain ⟨v, rfl⟩ := contract_surjective C hC q
    exact ⟨v, hq, rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem image_contract_self (C : Finset V) (hC : C.Nonempty) :
    C.image (contract C) = {none} := by
  ext q
  simp only [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (contract_none_iff C v).mpr hv
  · rintro rfl
    obtain ⟨v, hv⟩ := hC
    exact ⟨v, hv, (contract_none_iff C v).mpr hv⟩

omit [Fintype E] [DecidableEq E] in
theorem preimageSet_ne_self (C : Finset V) (hC : C.Nonempty)
    {S' : Finset (ContractV C)} (hS' : 2 ≤ S'.card) :
    preimageSet C S' ≠ C := by
  intro heq
  have himg := congrArg (fun A : Finset V => (A.image (contract C)).card) heq
  rw [image_preimageSet C hC S', image_contract_self C hC, Finset.card_singleton] at himg
  omega

omit [Fintype E] [DecidableEq E] in
theorem card_preimageSet_ge_two (C : Finset V) (hC : C.Nonempty)
    {S' : Finset (ContractV C)} (hS' : 2 ≤ S'.card) :
    2 ≤ (preimageSet C S').card := by
  have hle : ((preimageSet C S').image (contract C)).card ≤ (preimageSet C S').card :=
    Finset.card_image_le
  rw [image_preimageSet C hC S'] at hle
  omega

omit [Fintype E] [DecidableEq E] in
theorem preimageSet_erase_none_card (C : Finset V) (S' : Finset (ContractV C)) :
    ((preimageSet C S') \ C).card = (S'.erase none).card := by
  apply Finset.card_bij (fun v _ => contract C v)
  · intro v hv
    obtain ⟨hvS, hvC⟩ := Finset.mem_sdiff.mp hv
    exact Finset.mem_erase.mpr ⟨(contract_none_iff C v).not.mpr hvC,
      (mem_preimageSet C S' v).mp hvS⟩
  · intro u hu v hv heq
    obtain ⟨_, huC⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨_, hvC⟩ := Finset.mem_sdiff.mp hv
    rw [contract_some C ⟨u, huC⟩] at heq
    exact ((contract_eq_some_iff C v ⟨u, huC⟩).mp heq.symm).symm
  · intro q hq
    obtain ⟨hqn, hqS⟩ := Finset.mem_erase.mp hq
    cases q with
    | none => exact False.elim (hqn rfl)
    | some w =>
      refine ⟨w.val, Finset.mem_sdiff.mpr ⟨?_, w.property⟩, contract_some C w⟩
      rw [mem_preimageSet, contract_some C w]
      exact hqS

omit [Fintype E] [DecidableEq E] in
theorem card_preimageSet_of_none_mem (C : Finset V) {S' : Finset (ContractV C)}
    (hnone : none ∈ S') :
    (preimageSet C S').card = C.card + S'.card - 1 := by
  have hsub : C ⊆ preimageSet C S' := by
    intro v hv
    rw [mem_preimageSet, (contract_none_iff C v).mpr hv]
    exact hnone
  have hsdiff := Finset.card_sdiff_add_card_eq_card hsub
  rw [preimageSet_erase_none_card, Finset.card_erase_of_mem hnone] at hsdiff
  have hpos : 1 ≤ S'.card := Finset.card_pos.mpr ⟨none, hnone⟩
  omega

omit [Fintype E] [DecidableEq E] in
theorem card_preimageSet_of_none_notMem (C : Finset V) {S' : Finset (ContractV C)}
    (hnone : none ∉ S') :
    (preimageSet C S').card = S'.card := by
  have hdisj : Disjoint (preimageSet C S') C := by
    rw [Finset.disjoint_left]
    intro v hvS hvC
    have hc := (mem_preimageSet C S' v).mp hvS
    rw [(contract_none_iff C v).mpr hvC] at hc
    exact hnone hc
  have hsdiff : (preimageSet C S' \ C) = preimageSet C S' :=
    Finset.sdiff_eq_self_of_disjoint hdisj
  have hcard := preimageSet_erase_none_card C S'
  rw [hsdiff, Finset.erase_eq_of_notMem hnone] at hcard
  exact hcard

def liftYSet (C : Finset V) (yC : ℝ) (ySet' : Finset (ContractV C) → ℝ) (S : Finset V) : ℝ :=
  if S = C then yC
  else if S = preimageSet C (S.image (contract C)) ∧ 2 ≤ (S.image (contract C)).card then
    ySet' (S.image (contract C))
  else 0

omit [Fintype E] [DecidableEq E] in
theorem liftYSet_self (C : Finset V) (yC : ℝ) (ySet' : Finset (ContractV C) → ℝ) :
    liftYSet C yC ySet' C = yC := by
  simp [liftYSet]

omit [Fintype E] [DecidableEq E] in
theorem liftYSet_preimage (C : Finset V) (hC : C.Nonempty) (yC : ℝ)
    (ySet' : Finset (ContractV C) → ℝ) {S' : Finset (ContractV C)} (hS' : 2 ≤ S'.card) :
    liftYSet C yC ySet' (preimageSet C S') = ySet' S' := by
  have hne : preimageSet C S' ≠ C := preimageSet_ne_self C hC hS'
  have himg : (preimageSet C S').image (contract C) = S' := image_preimageSet C hC S'
  unfold liftYSet
  rw [if_neg hne, himg, if_pos ⟨rfl, hS'⟩]

omit [Fintype E] [DecidableEq E] in
theorem sum_liftYSet (C : Finset V) (hC : 2 ≤ C.card) (yC : ℝ)
    (ySet' : Finset (ContractV C) → ℝ) (Q : Finset V → Prop) [DecidablePred Q] :
    ∑ S ∈ Finset.univ.filter (fun S : Finset V => 2 ≤ S.card ∧ Q S),
      liftYSet C yC ySet' S =
    (if Q C then yC else 0) +
      ∑ S' ∈ Finset.univ.filter (fun S' : Finset (ContractV C) => 2 ≤ S'.card ∧ Q (preimageSet C S')),
        ySet' S' := by
  have hneC : C.Nonempty := Finset.card_pos.mp (by omega)
  let F := Finset.univ.filter (fun S : Finset V => 2 ≤ S.card ∧ Q S)
  let F1 := F.filter (fun S => S = C)
  let F2 := F.filter (fun S => S ≠ C)
  have hsplit : ∑ S ∈ F, liftYSet C yC ySet' S =
      (∑ S ∈ F1, liftYSet C yC ySet' S) + ∑ S ∈ F2, liftYSet C yC ySet' S := by
    rw [← Finset.sum_filter_add_sum_filter_not F (fun S => S = C)]
  rw [hsplit]
  congr 1
  · by_cases hQC : Q C
    · have hF1 : F1 = {C} := by
        ext S
        simp only [F1, F, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl
          exact ⟨⟨hC, hQC⟩, rfl⟩
      rw [if_pos hQC, hF1, Finset.sum_singleton, liftYSet_self]
    · have hF1 : F1 = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro S hSF hSC
        subst hSC
        exact hQC (Finset.mem_filter.mp hSF).2.2
      rw [if_neg hQC, hF1, Finset.sum_empty]
  · let F2' := F2.filter (fun S => S = preimageSet C (S.image (contract C)) ∧
      2 ≤ (S.image (contract C)).card)
    have hF2 : ∑ S ∈ F2, liftYSet C yC ySet' S = ∑ S ∈ F2', liftYSet C yC ySet' S := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro S hSF2 hnot
      have hne : S ≠ C := (Finset.mem_filter.mp hSF2).2
      have hcond : ¬ (S = preimageSet C (S.image (contract C)) ∧
          2 ≤ (S.image (contract C)).card) := fun hc => hnot (Finset.mem_filter.mpr ⟨hSF2, hc⟩)
      unfold liftYSet
      rw [if_neg hne, if_neg hcond]
    rw [hF2]
    symm
    apply Finset.sum_bij (fun S' _ => preimageSet C S')
    · intro S' hS'
      obtain ⟨hcard, hQ⟩ := (Finset.mem_filter.mp hS').2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, card_preimageSet_ge_two C hneC hcard, hQ⟩,
        preimageSet_ne_self C hneC hcard⟩, ?_⟩
      rw [image_preimageSet C hneC S']
      exact ⟨rfl, hcard⟩
    · intro S₁' h₁ S₂' h₂ heq
      rw [← image_preimageSet C hneC S₁', ← image_preimageSet C hneC S₂', heq]
    · intro S hS
      obtain ⟨hSF2, hpre, hcard⟩ := Finset.mem_filter.mp hS
      have hQS : Q S := (Finset.mem_filter.mp (Finset.mem_filter.mp hSF2).1).2.2
      refine ⟨S.image (contract C), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, ?_⟩,
        hpre.symm⟩
      simpa only [← hpre] using hQS
    · intro S' hS'
      obtain ⟨hcard, _⟩ := (Finset.mem_filter.mp hS').2
      rw [liftYSet_preimage C hneC yC ySet' hcard]

omit [Fintype E] [DecidableEq E] in
theorem nodeSetLoad_liftYSet (C : Finset V) (hC : 2 ≤ C.card) (yC : ℝ)
    (ySet' : Finset (ContractV C) → ℝ) (v : V) :
    nodeSetLoad (liftYSet C yC ySet') v =
      (if v ∈ C then yC else 0) + nodeSetLoad ySet' (contract C v) := by
  unfold nodeSetLoad
  rw [sum_liftYSet C hC yC ySet' (fun S => v ∈ S)]
  simp only [mem_preimageSet]

omit [Fintype E] [DecidableEq E] in
theorem edgeSetDual_liftYSet_internal (G : Graph V E) (C : Finset V) (hC : 2 ≤ C.card)
    (yC : ℝ) (ySet' : Finset (ContractV C) → ℝ) {e : E}
    (hf : G.front e ∈ C) (hr : G.rear e ∈ C) :
    edgeSetDual G (liftYSet C yC ySet') e = yC + nodeSetLoad ySet' none := by
  unfold edgeSetDual
  rw [sum_liftYSet C hC yC ySet' (fun S => G.front e ∈ S ∧ G.rear e ∈ S)]
  rw [if_pos ⟨hf, hr⟩]
  congr 1
  unfold nodeSetLoad
  apply Finset.sum_congr
  · ext S'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_preimageSet,
      (contract_none_iff C _).mpr hf, (contract_none_iff C _).mpr hr, and_self]
  · intro _ _; rfl

omit [Fintype E] [DecidableEq E] in
theorem edgeSetDual_liftYSet_contract (G : Graph V E) (C : Finset V) (hC : 2 ≤ C.card)
    (yC : ℝ) (ySet' : Finset (ContractV C) → ℝ) (e : ContractE G C) :
    edgeSetDual G (liftYSet C yC ySet') e.val =
      edgeSetDual (contractGraph G C) ySet' e := by
  unfold edgeSetDual
  rw [sum_liftYSet C hC yC ySet' (fun S => G.front e.val ∈ S ∧ G.rear e.val ∈ S)]
  have hnot : ¬ (G.front e.val ∈ C ∧ G.rear e.val ∈ C) :=
    (contract_front_ne_rear_iff G C e.val).mp e.property
  rw [if_neg hnot, zero_add, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S' _
  by_cases h1 : 2 ≤ S'.card ∧ contract C (G.front e.val) ∈ S' ∧ contract C (G.rear e.val) ∈ S' <;>
    simp [h1, mem_preimageSet, contractGraph]

/-! ### Section 4: Incidence Vector Filter Lemmas -/

omit [Fintype V] [DecidableEq V] in
theorem sum_incidenceVector_filter (B : Finset E) (Q : E → Prop) [DecidablePred Q] :
    ∑ e ∈ Finset.univ.filter Q, incidenceVector B e = ((B.filter Q).card : ℝ) := by
  unfold incidenceVector
  rw [Finset.sum_boole]
  norm_cast
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]

omit [Fintype V] in
theorem sum_incoming_incidenceVector_eq_one_iff (G : Graph V E) (B : Finset E)
    (hhead : ∀ e ∈ B, ∀ f ∈ B, G.front e = G.front f → e = f) (v : V) :
    (∑ e ∈ Finset.univ.filter (fun e => G.front e = v), incidenceVector B e = 1) ↔
      ∃ e ∈ B, G.front e = v := by
  rw [sum_incidenceVector_filter]
  norm_cast
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨e, he⟩
    have hmem : e ∈ B.filter (fun f => G.front f = v) := he ▸ Finset.mem_singleton_self e
    exact ⟨e, (Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2⟩
  · rintro ⟨e, heB, hev⟩
    refine ⟨e, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hfB, hfv⟩
      exact hhead f hfB e heB (hfv.trans hev.symm)
    · rintro rfl
      exact ⟨heB, hev⟩

/-! ### Section 5: Main Inductive Proof -/

universe u v

set_option maxHeartbeats 800000 in
private theorem exists_dual_cert_aux (N : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V = N →
      ∀ (E : Type v) [Fintype E] [DecidableEq E]
        (G : Graph V E) (c : E → ℝ),
        ∃ (B : Finset E) (yNode : V → ℝ) (ySet : Finset V → ℝ),
          (∀ e ∈ B, ∀ f ∈ B, G.front e = G.front f → e = f) ∧
          (∃ rank : V → ℕ, ∀ e ∈ B, rank (G.rear e) < rank (G.front e)) ∧
          IsDualCertificate G c B yNode ySet ∧
          (∀ v : V, yNode v + nodeSetLoad ySet v ≤ maxIn G c v) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V _ _ hcard E _ _ G c
    classical
    let m : V → ℝ := fun v => maxIn G c v
    let P : Finset V := Finset.univ.filter (fun v : V => 0 < m v)
    have hpick_ex : ∀ v : {v : V // v ∈ P}, ∃ e : E, G.front e = v.val ∧ c e = m v.val :=
      fun v => exists_eq_maxIn_of_pos G c v.val (Finset.mem_filter.mp v.property).2
    obtain ⟨pick, hpick_spec⟩ := Classical.axiomOfChoice hpick_ex
    have hpick_front : ∀ v : {v : V // v ∈ P}, G.front (pick v) = v.val :=
      fun v => (hpick_spec v).1
    have hpick_cost : ∀ v : {v : V // v ∈ P}, c (pick v) = m v.val :=
      fun v => (hpick_spec v).2
    let p : V → V := fun v => if hv : v ∈ P then G.rear (pick ⟨v, hv⟩) else v
    have hp_ne : ∀ v ∈ P, p v ≠ v := by
      intro v hv heq
      have h1 : p v = G.rear (pick ⟨v, hv⟩) := dif_pos hv
      have h2 : G.front (pick ⟨v, hv⟩) = v := hpick_front ⟨v, hv⟩
      exact G.front_ne_rear (pick ⟨v, hv⟩) (h2.trans (h1.symm.trans heq).symm)
    let U : Finset V := Finset.univ.filter (fun v : V => ∀ k : ℕ, p^[k] v ∈ P)
    by_cases hU : U.Nonempty
    · -- Inductive case: there is a directed cycle C of positive-weight maximum incoming edges
      have hU_closed : ∀ v ∈ U, p v ∈ U := by
        intro v hv
        have hall := (Finset.mem_filter.mp hv).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k => ?_⟩
        simpa only [Function.iterate_succ_apply] using hall (k + 1)
      have hU_sub_P : U ⊆ P := by
        intro v hv
        simpa using (Finset.mem_filter.mp hv).2 0
      obtain ⟨C, hCU⟩ := exists_parent_cycle p U hU hU_closed
      have hCP : C.support ⊆ P := hCU.trans hU_sub_P
      have hC_card : 2 ≤ C.support.card :=
        C.card_ge_two (fun v hv => hp_ne v (hCP hv))
      have hsmall : Fintype.card (ContractV C.support) < N := by
        rw [← hcard]
        exact contract_card_lt C.support hC_card
      obtain ⟨vStar, hvStarC, hvStarMin⟩ :=
        Finset.exists_min_image C.support m C.nonempty
      let M : ℝ := m vStar
      have hM_pos : 0 < M := (Finset.mem_filter.mp (hCP hvStarC)).2
      have hM_le : ∀ u ∈ C.support, M ≤ m u := fun u hu => hvStarMin u hu
      let delta : V → ℝ := fun v => if v ∈ C.support then m v - M else 0
      have hdelta_nonneg : ∀ v : V, 0 ≤ delta v := by
        intro v
        dsimp [delta]
        split_ifs with hv
        · linarith [hM_le v hv]
        · exact le_rfl
      let cTilde : E → ℝ := fun e => c e - delta (G.front e)
      have hcTilde_C : ∀ e : E, G.front e ∈ C.support → cTilde e ≤ M := by
        intro e hf
        have hle : c e ≤ m (G.front e) := le_maxIn G c rfl
        simp only [cTilde, delta, if_pos hf]
        linarith
      have hcTilde_notC : ∀ e : E, G.front e ∉ C.support → cTilde e = c e := by
        intro e hf
        simp [cTilde, delta, if_neg hf]
      have hpick_cTilde : ∀ u : {v : V // v ∈ P}, u.val ∈ C.support → cTilde (pick u) = M := by
        intro u huC
        simp only [cTilde, hpick_front, delta, if_pos huC, hpick_cost]
        ring
      let G' := contractGraph G C.support
      let c' : ContractE G C.support → ℝ := fun e => cTilde e.val
      obtain ⟨B', yNode', ySet', hhead', ⟨rank', hrank'⟩, hcert', hload'⟩ :=
        ih (Fintype.card (ContractV C.support)) hsmall
          (ContractV C.support) rfl (ContractE G C.support) G' c'
      have hmaxIn_none : maxIn G' c' none ≤ M := by
        rw [maxIn_le_iff]
        refine ⟨le_of_lt hM_pos, fun e he => ?_⟩
        have hf : G.front e.val ∈ C.support := (contract_none_iff C.support _).mp he
        exact hcTilde_C e.val hf
      have hmaxIn_some : ∀ v : {v : V // v ∉ C.support}, maxIn G' c' (some v) ≤ m v.val := by
        intro v
        rw [maxIn_le_iff]
        refine ⟨maxIn_nonneg G c v.val, fun e he => ?_⟩
        have hf : G.front e.val = v.val := (contract_eq_some_iff C.support _ v).mp he
        have hnotC : G.front e.val ∉ C.support := hf ▸ v.property
        rw [ show c' e = c e.val from hcTilde_notC e.val hnotC ]
        exact le_maxIn G c hf
      have hload_none : yNode' none + nodeSetLoad ySet' none ≤ M :=
        (hload' none).trans hmaxIn_none
      let yC : ℝ := M - (yNode' none + nodeSetLoad ySet' none)
      have hyC_nonneg : 0 ≤ yC := by dsimp [yC]; linarith
      -- Entry vertex in C.support
      let h_in_prop : Prop := ∃ e' ∈ B', G'.front e' = none
      let entry : V :=
        if h_in : h_in_prop then G.front (Classical.choose h_in).val else vStar
      have hentryC : entry ∈ C.support := by
        dsimp [entry]
        split_ifs with h_in
        · have he' := (Classical.choose_spec h_in).2
          exact (contract_none_iff C.support _).mp he'
        · exact hvStarC
      -- Lifted branching B = B1 ∪ B2
      let B1 : Finset E := B'.image Subtype.val
      let C_rem : Finset V := C.support.erase entry
      obtain ⟨cycleEdge, hcycleEdge_front, hcycleEdge_rear, hcycleEdge_cost⟩ :
          ∃ cycleEdge : {u : V // u ∈ C_rem} → E,
            (∀ u, G.front (cycleEdge u) = u.val) ∧
            (∀ u, G.rear (cycleEdge u) = p u.val) ∧
            (∀ u, c (cycleEdge u) = m u.val) :=
        ⟨fun u => pick ⟨u.val, hCP (Finset.mem_of_mem_erase u.property)⟩,
          fun _ => hpick_front _,
          fun u => by
            have huP : u.val ∈ P := hCP (Finset.mem_of_mem_erase u.property)
            simp [p, dif_pos huP],
          fun _ => hpick_cost _⟩
      have hcycleEdge_inj : Function.Injective cycleEdge := by
        intro u w heq
        apply Subtype.ext
        rw [← hcycleEdge_front u, ← hcycleEdge_front w, heq]
      let B2 : Finset E := Finset.univ.image cycleEdge
      let B : Finset E := B1 ∪ B2
      have hB1_not_internal : ∀ e ∈ B1, ¬ (G.front e ∈ C.support ∧ G.rear e ∈ C.support) := by
        intro e he
        obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
        exact (contract_front_ne_rear_iff G C.support e'.val).mp e'.property
      have hB2_internal : ∀ e ∈ B2, G.front e ∈ C.support ∧ G.rear e ∈ C.support := by
        intro e he
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
        have huC : u.val ∈ C.support := Finset.mem_of_mem_erase u.property
        rw [hcycleEdge_front, hcycleEdge_rear]
        exact ⟨huC, C.maps u.val huC⟩
      have hdisj_B1_B2 : Disjoint B1 B2 := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        exact hB1_not_internal e he1 (hB2_internal e he2)
      have hB1_front_in_C : ∀ e' ∈ B', G.front e'.val ∈ C.support →
          G.front e'.val = entry := by
        intro e' he'B hfC
        have he'none : G'.front e' = none := (contract_none_iff C.support _).mpr hfC
        have hin : h_in_prop := ⟨e', he'B, he'none⟩
        have hchoose := Classical.choose_spec hin
        have heq : e' = Classical.choose hin :=
          hhead' e' he'B (Classical.choose hin) hchoose.1 (he'none.trans hchoose.2.symm)
        dsimp [entry]
        rw [dif_pos hin, ← heq]
      have hhead : ∀ e ∈ B, ∀ f ∈ B, G.front e = G.front f → e = f := by
        intro e he f hf hef
        rcases Finset.mem_union.mp he with he1 | he2 <;>
          rcases Finset.mem_union.mp hf with hf1 | hf2
        · obtain ⟨e', he'B, rfl⟩ := Finset.mem_image.mp he1
          obtain ⟨f', hf'B, rfl⟩ := Finset.mem_image.mp hf1
          have hfeq : G'.front e' = G'.front f' := by
            change contract C.support (G.front e'.val) = contract C.support (G.front f'.val)
            rw [hef]
          exact congrArg Subtype.val (hhead' e' he'B f' hf'B hfeq)
        · obtain ⟨e', he'B, rfl⟩ := Finset.mem_image.mp he1
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hf2
          rw [hcycleEdge_front] at hef
          have hwC : w.val ∈ C.support := Finset.mem_of_mem_erase w.property
          have hne_entry : w.val ≠ entry := (Finset.mem_erase.mp w.property).1
          have hent := hB1_front_in_C e' he'B (hef ▸ hwC)
          exact False.elim (hne_entry (hef.symm.trans hent))
        · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he2
          obtain ⟨f', hf'B, rfl⟩ := Finset.mem_image.mp hf1
          rw [hcycleEdge_front] at hef
          have huC : u.val ∈ C.support := Finset.mem_of_mem_erase u.property
          have hne_entry : u.val ≠ entry := (Finset.mem_erase.mp u.property).1
          have hent := hB1_front_in_C f' hf'B (hef.symm ▸ huC)
          exact False.elim (hne_entry (hef.trans hent))
        · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he2
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hf2
          rw [hcycleEdge_front, hcycleEdge_front] at hef
          exact congrArg cycleEdge (Subtype.ext hef)
      -- Rank function on V
      obtain ⟨K, hK⟩ := ParentCycle.rank_bounded C entry
      have hK0 : 0 < K := lt_of_le_of_lt (Nat.zero_le _) (hK entry hentryC)
      let off (v : V) : ℕ := if v ∈ C.support then hitRank p entry v else 0
      have hoff : ∀ v : V, off v < K := by
        intro v
        dsimp [off]
        split_ifs with hv
        · exact hK v hv
        · exact hK0
      let rank (v : V) : ℕ := K * rank' (contract C.support v) + off v
      have hrank : ∀ e ∈ B, rank (G.rear e) < rank (G.front e) := by
        intro e he
        rcases Finset.mem_union.mp he with he1 | he2
        · obtain ⟨e', he'B, rfl⟩ := Finset.mem_image.mp he1
          have hlt := hrank' e' he'B
          exact scaled_rank_lt K _ _ _ _ hlt (hoff _)
        · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he2
          have huC : u.val ∈ C.support := Finset.mem_of_mem_erase u.property
          have hne_entry : u.val ≠ entry := (Finset.mem_erase.mp u.property).1
          have hpC : p u.val ∈ C.support := C.maps u.val huC
          rw [hcycleEdge_front, hcycleEdge_rear]
          dsimp [rank]
          rw [(contract_none_iff C.support u.val).mpr huC,
            (contract_none_iff C.support (p u.val)).mpr hpC]
          simp only [off, if_pos huC, if_pos hpC]
          exact Nat.add_lt_add_left (ParentCycle.rank_parent_lt C entry hentryC u.val huC hne_entry) _
      -- Dual variables yNode and ySet
      let yNode : V → ℝ := fun v => delta v + yNode' (contract C.support v)
      let ySet : Finset V → ℝ := liftYSet C.support yC ySet'
      have hyNode_nonneg : ∀ v : V, 0 ≤ yNode v := by
        intro v
        exact add_nonneg (hdelta_nonneg v) (hcert'.1.1 (contract C.support v))
      have hySet_nonneg : ∀ S : Finset V, 2 ≤ S.card → 0 ≤ ySet S := by
        intro S _
        dsimp [ySet, liftYSet]
        split_ifs with h1 h2
        · exact hyC_nonneg
        · exact hcert'.1.2.1 _ h2.2
        · exact le_rfl
      have hload_eq : ∀ v : V,
          yNode v + nodeSetLoad ySet v =
            if v ∈ C.support then m v
            else yNode' (contract C.support v) + nodeSetLoad ySet' (contract C.support v) := by
        intro v
        rw [nodeSetLoad_liftYSet C.support hC_card yC ySet' v]
        dsimp [yNode, delta, yC]
        split_ifs with hv
        · rw [(contract_none_iff C.support v).mpr hv]
          ring
        · ring
      have hload_le : ∀ v : V, yNode v + nodeSetLoad ySet v ≤ maxIn G c v := by
        intro v
        rw [hload_eq v]
        split_ifs with hv
        · exact le_rfl
        · rw [contract_some C.support ⟨v, hv⟩]
          exact (hload' (some ⟨v, hv⟩)).trans (hmaxIn_some ⟨v, hv⟩)
      have hdual_edge : ∀ e : E,
          yNode (G.front e) + edgeSetDual G ySet e =
            if h : G.front e ∈ C.support ∧ G.rear e ∈ C.support then m (G.front e)
            else delta (G.front e) +
              (yNode' (G'.front ⟨e, (contract_front_ne_rear_iff G C.support e).mpr h⟩) +
                edgeSetDual G' ySet' ⟨e, (contract_front_ne_rear_iff G C.support e).mpr h⟩) := by
        intro e
        by_cases h : G.front e ∈ C.support ∧ G.rear e ∈ C.support
        · rw [dif_pos h, edgeSetDual_liftYSet_internal G C.support hC_card yC ySet' h.1 h.2]
          dsimp [yNode, delta, yC]
          rw [if_pos h.1, (contract_none_iff C.support _).mpr h.1]
          ring
        · rw [dif_neg h]
          let e' : ContractE G C.support := ⟨e, (contract_front_ne_rear_iff G C.support e).mpr h⟩
          have heq := edgeSetDual_liftYSet_contract G C.support hC_card yC ySet' e'
          dsimp only [yNode, G']
          rw [heq, add_assoc]
          rfl
      have hdual_feas_edge : ∀ e : E, c e ≤ yNode (G.front e) + edgeSetDual G ySet e := by
        intro e
        rw [hdual_edge e]
        split_ifs with h
        · exact le_maxIn G c rfl
        · let e' : ContractE G C.support := ⟨e, (contract_front_ne_rear_iff G C.support e).mpr h⟩
          have hfe' := hcert'.1.2.2 e'
          change cTilde e ≤ _ at hfe'
          dsimp [cTilde] at hfe'
          linarith
      have htight : ∀ e ∈ B, yNode (G.front e) + edgeSetDual G ySet e = c e := by
        intro e he
        rw [hdual_edge e]
        rcases Finset.mem_union.mp he with he1 | he2
        · have hnot : ¬ (G.front e ∈ C.support ∧ G.rear e ∈ C.support) :=
            hB1_not_internal e he1
          rw [dif_neg hnot]
          obtain ⟨e', he'B, rfl⟩ := Finset.mem_image.mp he1
          have ht' := hcert'.2.2.2 e' he'B
          change _ = cTilde e'.val at ht'
          dsimp [cTilde] at ht'
          linarith
        · have hint : G.front e ∈ C.support ∧ G.rear e ∈ C.support :=
            hB2_internal e he2
          rw [dif_pos hint]
          obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he2
          rw [hcycleEdge_front, hcycleEdge_cost]
      -- Node complementary slackness (18)
      have hcs_node : ∀ v : V, yNode v ≠ 0 →
          ∑ e ∈ Finset.univ.filter (fun e => G.front e = v), incidenceVector B e = 1 := by
        intro v hy
        rw [sum_incoming_incidenceVector_eq_one_iff G B hhead v]
        by_cases hvC : v ∈ C.support
        · by_cases hve : v = entry
          · subst hve
            by_cases hin : h_in_prop
            · have hchoose := Classical.choose_spec hin
              refine ⟨(Classical.choose hin).val, Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨Classical.choose hin, hchoose.1, rfl⟩), ?_⟩
              dsimp [entry]
              rw [dif_pos hin]
            · have hent_eq : entry = vStar := by dsimp [entry]; rw [dif_neg hin]
              have hy_none_zero : yNode' none = 0 := by
                by_contra hne
                have hsum1 := hcert'.2.1 none hne
                rw [sum_incoming_incidenceVector_eq_one_iff G' B' hhead' none] at hsum1
                exact hin hsum1
              have hy_zero : yNode entry = 0 := by
                dsimp [yNode, delta]
                rw [if_pos hentryC, (contract_none_iff C.support entry).mpr hentryC,
                  hent_eq, hy_none_zero]
                dsimp [M]
                ring
              exact False.elim (hy hy_zero)
          · have hv_rem : v ∈ C_rem := Finset.mem_erase.mpr ⟨hve, hvC⟩
            refine ⟨cycleEdge ⟨v, hv_rem⟩, Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨⟨v, hv_rem⟩, Finset.mem_univ _, rfl⟩),
              hcycleEdge_front ⟨v, hv_rem⟩⟩
        · have hy' : yNode' (some ⟨v, hvC⟩) ≠ 0 := by
            dsimp [yNode, delta] at hy
            rw [if_neg hvC, zero_add, contract_some C.support ⟨v, hvC⟩] at hy
            exact hy
          have hsum1 := hcert'.2.1 (some ⟨v, hvC⟩) hy'
          rw [sum_incoming_incidenceVector_eq_one_iff G' B' hhead' (some ⟨v, hvC⟩)] at hsum1
          obtain ⟨e', he'B, he'v⟩ := hsum1
          refine ⟨e'.val, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e', he'B, rfl⟩), ?_⟩
          exact (contract_eq_some_iff C.support _ ⟨v, hvC⟩).mp he'v
      -- Set complementary slackness (19)
      have hB2_card : B2.card = C.support.card - 1 := by
        dsimp [B2, C_rem]
        rw [Finset.card_image_of_injective _ hcycleEdge_inj]
        simp [Finset.card_erase_of_mem hentryC]
      have hcs_set : ∀ S : Finset V, 2 ≤ S.card → ySet S ≠ 0 →
          ∑ e ∈ Finset.univ.filter (fun e => G.front e ∈ S ∧ G.rear e ∈ S), incidenceVector B e =
            (S.card : ℝ) - 1 := by
        intro S hScard hyS
        let Q : E → Prop := fun e => G.front e ∈ S ∧ G.rear e ∈ S
        rw [sum_incidenceVector_filter B Q]
        have hB_split : (B.filter Q).card = (B1.filter Q).card + (B2.filter Q).card := by
          dsimp [B]
          rw [Finset.filter_union]
          exact Finset.card_union_of_disjoint
            (hdisj_B1_B2.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))
        rw [hB_split]
        dsimp [ySet, liftYSet] at hyS
        by_cases hSC : S = C.support
        · subst hSC
          have hB1_empty : B1.filter Q = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro e he1
            exact hB1_not_internal e he1
          have hB2_all : B2.filter Q = B2 := by
            rw [Finset.filter_eq_self]
            intro e he2
            exact hB2_internal e he2
          rw [hB1_empty, hB2_all, Finset.card_empty, zero_add, hB2_card]
          have hpos : 1 ≤ C.support.card := by omega
          rw [Nat.cast_sub hpos, Nat.cast_one]
        · rw [if_neg hSC] at hyS
          by_cases hpre : S = preimageSet C.support (S.image (contract C.support)) ∧
              2 ≤ (S.image (contract C.support)).card
          · rw [if_pos hpre] at hyS
            let S' := S.image (contract C.support)
            have hS_eq : S = preimageSet C.support S' := hpre.1
            have hS'_card : 2 ≤ S'.card := hpre.2
            have hcs' := hcert'.2.2.1 S' hS'_card hyS
            let Q' : ContractE G C.support → Prop :=
              fun e' => G'.front e' ∈ S' ∧ G'.rear e' ∈ S'
            rw [sum_incidenceVector_filter B' Q'] at hcs'
            have hB1_card : (B1.filter Q).card = (B'.filter Q').card := by
              have h_eq : B1.filter Q = (B'.filter Q').image Subtype.val := by
                ext e
                simp only [B1, Q, Q', G', contractGraph, Finset.mem_filter, Finset.mem_image,
                  hS_eq, mem_preimageSet]
                constructor
                · rintro ⟨⟨e', he'B, rfl⟩, hfS, hrS⟩
                  exact ⟨e', ⟨he'B, hfS, hrS⟩, rfl⟩
                · rintro ⟨e', ⟨he'B, hfS, hrS⟩, rfl⟩
                  exact ⟨⟨e', he'B, rfl⟩, hfS, hrS⟩
              rw [h_eq, Finset.card_image_of_injective _ Subtype.val_injective]
            rw [hB1_card]
            by_cases hnone : none ∈ S'
            · have hB2_all : B2.filter Q = B2 := by
                rw [Finset.filter_eq_self]
                intro e he2
                obtain ⟨hfC, hrC⟩ := hB2_internal e he2
                dsimp [Q]
                rw [hS_eq]
                refine ⟨?_, ?_⟩
                · rw [mem_preimageSet, (contract_none_iff C.support _).mpr hfC]; exact hnone
                · rw [mem_preimageSet, (contract_none_iff C.support _).mpr hrC]; exact hnone
              have hcard_S : S.card = C.support.card + S'.card - 1 := by
                rw [hS_eq]
                exact card_preimageSet_of_none_mem C.support hnone
              rw [hB2_all, hB2_card, hcard_S]
              have hposC : 1 ≤ C.support.card := by omega
              have hposCS : 1 ≤ C.support.card + S'.card := by omega
              push_cast [Nat.cast_sub hposC, Nat.cast_sub hposCS]
              linarith
            · have hB2_empty : B2.filter Q = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                intro e he2 hQe
                dsimp [Q] at hQe
                obtain ⟨hfS, _⟩ := hQe
                obtain ⟨hfC, _⟩ := hB2_internal e he2
                rw [hS_eq, mem_preimageSet, (contract_none_iff C.support _).mpr hfC] at hfS
                exact hnone hfS
              have hcard_S : S.card = S'.card := by
                rw [hS_eq]
                exact card_preimageSet_of_none_notMem C.support hnone
              rw [hB2_empty, Finset.card_empty, add_zero, hcard_S]
              exact hcs'
          · rw [if_neg hpre] at hyS
            exact False.elim (hyS rfl)
      refine ⟨B, yNode, ySet, hhead, ⟨rank, hrank⟩,
        ⟨⟨hyNode_nonneg, hySet_nonneg, hdual_feas_edge⟩, hcs_node, hcs_set, htight⟩,
        hload_le⟩
    · -- Base case: U is empty, so every vertex eventually leaves P under p
      have hex_leave : ∀ v : V, ∃ k : ℕ, p^[k] v ∉ P := by
        intro v
        by_contra hall
        push_neg at hall
        exact hU ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hall⟩⟩
      let rank : V → ℕ := fun v => Nat.find (hex_leave v)
      have hrank_p : ∀ v ∈ P, rank (p v) < rank v := by
        intro v hvP
        have hn0 : Nat.find (hex_leave v) ≠ 0 := by
          intro h0
          have hspec := Nat.find_spec (hex_leave v)
          rw [h0] at hspec
          exact hspec hvP
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        have hspec : p^[k] (p v) ∉ P := by
          have hs := Nat.find_spec (hex_leave v)
          rw [hk, Function.iterate_succ_apply] at hs
          exact hs
        dsimp [rank]
        rw [hk]
        exact Nat.lt_succ_of_le (Nat.find_min' (hex_leave (p v)) hspec)
      let B : Finset E := Finset.univ.image pick
      have hhead : ∀ e ∈ B, ∀ f ∈ B, G.front e = G.front f → e = f := by
        intro e he f hf hef
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hf
        rw [hpick_front, hpick_front] at hef
        exact congrArg pick (Subtype.ext hef)
      have hrank : ∀ e ∈ B, rank (G.rear e) < rank (G.front e) := by
        intro e he
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
        have hp_eq : G.rear (pick u) = p u.val := by simp [p, dif_pos u.property]
        rw [hpick_front, hp_eq]
        exact hrank_p u.val u.property
      let yNode : V → ℝ := m
      let ySet : Finset V → ℝ := fun _ => 0
      have hySet_zero : ∀ e : E, edgeSetDual G ySet e = 0 := by
        intro e
        simp [edgeSetDual, ySet]
      have hload_zero : ∀ v : V, nodeSetLoad ySet v = 0 := by
        intro v
        simp [nodeSetLoad, ySet]
      refine ⟨B, yNode, ySet, hhead, ⟨rank, hrank⟩,
        ⟨⟨fun v => maxIn_nonneg G c v, fun _ _ => le_rfl, fun e => ?_⟩,
          fun v hy => ?_, fun S _ hyS => False.elim (hyS rfl), fun e he => ?_⟩,
        fun v => ?_⟩
      · rw [hySet_zero, add_zero]
        exact le_maxIn G c rfl
      · rw [sum_incoming_incidenceVector_eq_one_iff G B hhead v]
        have hpos : 0 < m v := lt_of_le_of_ne (maxIn_nonneg G c v) (Ne.symm hy)
        have hvP : v ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hpos⟩
        exact ⟨pick ⟨v, hvP⟩, Finset.mem_image.mpr ⟨⟨v, hvP⟩, Finset.mem_univ _, rfl⟩,
          hpick_front ⟨v, hvP⟩⟩
      · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
        rw [hySet_zero, add_zero, hpick_front, hpick_cost]
      · rw [hload_zero, add_zero]

end OptimumBranchings.Polytope.DualCertProof

theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : OptimumBranchings.Polytope.Graph V E) (c : E → ℝ) :
    ∃ (B : Finset E) (yNode : V → ℝ) (ySet : Finset V → ℝ),
      G.IsBranching B ∧ OptimumBranchings.Polytope.IsDualCertificate G c B yNode ySet := by
  obtain ⟨B, yNode, ySet, hhead, ⟨rank, hrank⟩, hcert, _⟩ :=
    OptimumBranchings.Polytope.DualCertProof.exists_dual_cert_aux (Fintype.card V) V rfl E G c
  exact ⟨B, yNode, ySet,
    OptimumBranchings.Polytope.DualCertProof.branching_of_rank G B hhead rank hrank, hcert⟩
