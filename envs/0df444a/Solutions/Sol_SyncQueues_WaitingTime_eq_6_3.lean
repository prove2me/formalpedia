-- Prove2me | solution 1 for SyncQueues.WaitingTime.eq_6_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:23:57.625324+00:00
-- url     : https://prove2.me/submissions/e778e9a3-6cf2-4121-abc2-c949ff093a03

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open SyncQueues.WaitingTime

namespace SQE63

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

lemma meas_sInf_nat {S : Ω → Set ℕ} (hS : ∀ k, MeasurableSet {ω | k ∈ S ω}) :
    Measurable (fun ω => sInf (S ω)) := by
  apply measurable_to_countable'
  intro j
  have hset : (fun ω => sInf (S ω)) ⁻¹' {j} =
      ({ω | j ∈ S ω} ∩ ⋂ k ∈ Finset.range j, {ω | k ∉ S ω}) ∪
        ({ω | j = 0} ∩ ⋂ k, {ω | k ∉ S ω}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range]
    constructor
    · intro h
      by_cases hne : (S ω).Nonempty
      · left
        refine ⟨h ▸ Nat.sInf_mem hne, fun k hk => ?_⟩
        exact Nat.notMem_of_lt_sInf (h ▸ hk)
      · right
        have he : S ω = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
        refine ⟨by rw [← h, he, Nat.sInf_empty], fun k hk => ?_⟩
        rw [he] at hk; exact hk
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · apply le_antisymm (Nat.sInf_le h1)
        by_contra hlt
        push_neg at hlt
        exact h2 _ hlt (Nat.sInf_mem ⟨j, h1⟩)
      · have he : S ω = ∅ := Set.eq_empty_iff_forall_notMem.2 h2
        rw [he, Nat.sInf_empty, h1]
  rw [hset]
  refine (MeasurableSet.inter (hS j) (MeasurableSet.biInter (Set.to_countable _)
    fun k _ => (hS k).compl)).union (MeasurableSet.inter ?_ (MeasurableSet.iInter fun k =>
      (hS k).compl))
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj]

lemma meas_index {ι β : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace β] {K : Ω → ι} (hK : Measurable K) {F : ι → Ω → β}
    (hF : ∀ i, Measurable (F i)) : Measurable (fun ω => F (K ω) ω) := by
  intro s hs
  have : (fun ω => F (K ω) ω) ⁻¹' s = ⋃ i, (K ⁻¹' {i}) ∩ (F i ⁻¹' s) := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iUnion fun i => (hK (measurableSet_singleton i)).inter (hF i hs)

lemma meas_countable_set {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {f : Ω → α} (hf : Measurable f) (s : Set α) :
    MeasurableSet (f ⁻¹' s) :=
  hf s.to_countable.measurableSet

variable {m : ℕ} {E : ℕ → Ω → ℝ} {R : ℕ → Ω → (Fin m → ℕ)} {C : ℕ → Ω → (Fin m → ℝ)}

lemma meas_predJob (hR : ∀ k, Measurable (R k)) (k : ℕ) (i : Fin m) :
    Measurable (fun ω => predJob (fun k => R k ω) k i) := by
  unfold predJob
  apply meas_sInf_nat
  intro k'
  have : {ω | k' ∈ {k'' | k < k'' ∧ R k ω i ∈ Set.range (R k'' ω)}} =
      (fun ω => (R k ω, R k' ω)) ⁻¹' {p | k < k' ∧ p.1 i ∈ Set.range p.2} := by
    ext ω; simp
  rw [this]
  exact meas_countable_set ((hR k).prodMk (hR k')) _

lemma meas_predJob' (hR : ∀ k, Measurable (R k)) {K : Ω → ℕ} (hK : Measurable K) (i : Fin m) :
    Measurable (fun ω => predJob (fun k => R k ω) (K ω) i) :=
  meas_index hK (F := fun k ω => predJob (fun k => R k ω) k i) fun k => meas_predJob hR k i

lemma meas_R_at (hR : ∀ k, Measurable (R k)) {K : Ω → ℕ} (hK : Measurable K) :
    Measurable (fun ω => R (K ω) ω) :=
  meas_index hK (F := fun k ω => R k ω) hR

lemma meas_predPiece (hR : ∀ k, Measurable (R k)) (k : ℕ) (i : Fin m) :
    Measurable (fun ω => predPiece (fun k => R k ω) k i) := by
  have h1 : Measurable (fun ω => (R (predJob (fun k => R k ω) k i) ω, R k ω i)) :=
    (meas_R_at hR (meas_predJob hR k i)).prodMk ((measurable_pi_apply i).comp (hR k))
  have h2 := (measurable_of_countable (fun p : (Fin m → ℕ) × ℕ =>
    if h : ∃ i', p.1 i' = p.2 then h.choose else i)).comp h1
  exact h2

lemma meas_arrival (hE : ∀ k, Measurable (E k)) (k : ℕ) :
    Measurable (fun ω => arrival (fun k => E k ω) k) := by
  unfold arrival
  split_ifs
  · exact hE 0
  · exact (Finset.measurable_sum _ fun j _ => hE j).neg

lemma meas_edgeHat (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (k : ℕ) (i : Fin m) :
    Measurable (fun ω => edgeHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) k i) := by
  unfold edgeHat
  have hJ := meas_predJob hR k i
  have hCJ : Measurable (fun ω => C (predJob (fun k => R k ω) k i) ω) :=
    meas_index hJ (F := fun k ω => C k ω) hC
  have hCJP : Measurable (fun ω => C (predJob (fun k => R k ω) k i) ω
      (predPiece (fun k => R k ω) k i)) :=
    meas_index (meas_predPiece hR k i) (F := fun i' ω => C (predJob (fun k => R k ω) k i) ω i')
      (fun i' => (measurable_pi_apply i').comp hCJ)
  have hA : Measurable (fun ω => arrival (fun k => E k ω) (predJob (fun k => R k ω) k i)) :=
    meas_index hJ (F := fun k ω => arrival (fun k => E k ω) k) (meas_arrival hE)
  exact hCJP.sub ((meas_arrival hE k).sub hA)

lemma meas_foldl (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (j : List (Fin m)) :
    ∀ st : Ω → ℕ × ℝ, Measurable st →
      Measurable (fun ω => j.foldl (fun (st : ℕ × ℝ) i =>
        (predJob (fun k => R k ω) st.1 i,
          st.2 + edgeHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) st.1 i)) (st ω)) := by
  induction j with
  | nil => intro st hst; simpa using hst
  | cons i j ih =>
    intro st hst
    simp only [List.foldl_cons]
    apply ih
    refine Measurable.prodMk ?_ ?_
    · exact meas_index hst.fst (F := fun k ω => predJob (fun k => R k ω) k i)
        (fun k => meas_predJob hR k i)
    · exact hst.snd.add (meas_index hst.fst
        (F := fun k ω => edgeHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) k i)
        (fun k => meas_edgeHat hE hR hC k i))

lemma meas_pathSumHat (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (j : List (Fin m)) :
    Measurable (fun ω => pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) j) := by
  unfold pathSumHat
  exact (meas_foldl hE hR hC j (fun _ => ((0 : ℕ), (0 : ℝ))) measurable_const).snd

lemma meas_Uhat (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (r : ℕ) :
    Measurable (fun ω => Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r) := by
  unfold Uhat
  exact Measurable.iSup fun v => meas_pathSumHat hE hR hC _

lemma meas_UhatUpTo (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (r : ℕ) :
    Measurable (fun ω => UhatUpTo (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r) := by
  unfold UhatUpTo
  exact Finset.measurable_range_sup'' fun n _ => meas_Uhat hE hR hC n

lemma meas_Wn (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) :
    Measurable (fun ω => Wn (fun k => E k ω) (fun k => R k ω) (fun k => C k ω)) := by
  unfold Wn
  exact Measurable.iSup fun r => meas_Uhat hE hR hC r

end Meas


section Det

variable {m : ℕ} {E : ℕ → ℝ} {R : ℕ → Fin m → ℕ} {C : ℕ → Fin m → ℝ}

lemma predJob_spec (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) (k : ℕ) (i : Fin m) :
    k < predJob R k i ∧ R k i ∈ Set.range (R (predJob R k i)) ∧
      ∀ k'', k < k'' → k'' < predJob R k i → R k i ∉ Set.range (R k'') := by
  have hne : ({k' : ℕ | k < k' ∧ R k i ∈ Set.range (R k')}).Nonempty := hpred k i
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun k'' h1 h2 h3 => ?_⟩
  exact Nat.notMem_of_lt_sInf h2 ⟨h1, h3⟩

/-- path sums from job `k` -/
noncomputable def pf (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ) : ℕ → List (Fin m) → ℝ
  | _, [] => 0
  | k, i :: j => edgeHat E R C k i + pf E R C (predJob R k i) j

lemma foldl_pf (j : List (Fin m)) : ∀ (k : ℕ) (c : ℝ),
    (j.foldl (fun (st : ℕ × ℝ) i => (predJob R st.1 i, st.2 + edgeHat E R C st.1 i)) (k, c)).2 =
      c + pf E R C k j := by
  induction j with
  | nil => intro k c; simp [pf]
  | cons i j ih =>
    intro k c
    simp only [List.foldl_cons]
    rw [ih]
    simp only [pf]
    ring

lemma pathSumHat_eq (j : List (Fin m)) : pathSumHat E R C j = pf E R C 0 j := by
  unfold pathSumHat
  rw [foldl_pf, zero_add]


end Det

/-! ### Paths on a sequence of job triples -/

abbrev Tr (m : ℕ) := ℝ × (Fin m → ℕ) × (Fin m → ℝ)

def shiftS {m : ℕ} (p : ℕ) (z : ℕ → Tr m) : ℕ → Tr m := fun k => z (p + k)

noncomputable def srch {m : ℕ} (z : ℕ → Tr m) (s : ℕ) : ℕ := sInf {k | s ∈ Set.range (z k).2.1}

noncomputable def posS {m : ℕ} (ρ : Fin m → ℕ) (s : ℕ) (fb : Fin m) : Fin m :=
  if h : ∃ i, ρ i = s then h.choose else fb

noncomputable def stepX {m : ℕ} (z : ℕ → Tr m) (ρ : Fin m → ℕ) (i : Fin m) : ℝ :=
  (z (srch z (ρ i))).2.2 (posS (z (srch z (ρ i))).2.1 (ρ i) i) -
    ∑ k ∈ Finset.range (srch z (ρ i) + 1), (z k).1

noncomputable def cs {m : ℕ} : (ℕ → Tr m) → (Fin m → ℕ) → List (Fin m) → ℝ
  | _, _, [] => 0
  | z, ρ, i :: v => stepX z ρ i + cs (shiftS (srch z (ρ i) + 1) z) (z (srch z (ρ i))).2.1 v

section Rel

lemma shiftS_shiftS {m : ℕ} (a b : ℕ) (z : ℕ → Tr m) : shiftS a (shiftS b z) = shiftS (b + a) z := by
  funext j; unfold shiftS; rw [add_assoc]

variable {m : ℕ} {E : ℕ → ℝ} {R : ℕ → Fin m → ℕ} {C : ℕ → Fin m → ℝ}

lemma predJob_eq_srch (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) (k : ℕ) (i : Fin m) :
    predJob R k i = k + 1 + srch (shiftS (k + 1) (fun k => (E k, R k, C k))) (R k i) := by
  unfold predJob srch shiftS
  set A : Set ℕ := {k' | k < k' ∧ R k i ∈ Set.range (R k')}
  set B : Set ℕ := {j | R k i ∈ Set.range (((fun k => (E k, R k, C k)) (k + 1 + j)).2.1)}
  have hA : A.Nonempty := hpred k i
  have hAm := Nat.sInf_mem hA
  have hB : (sInf A - (k + 1)) ∈ B := by
    show R k i ∈ Set.range (R (k + 1 + (sInf A - (k + 1))))
    rw [show k + 1 + (sInf A - (k + 1)) = sInf A by have := hAm.1; omega]
    exact hAm.2
  have hBm := Nat.sInf_mem ⟨_, hB⟩
  have h1 : sInf B ≤ sInf A - (k + 1) := Nat.sInf_le hB
  have h2 : sInf A ≤ k + 1 + sInf B := Nat.sInf_le (show k + 1 + sInf B ∈ A from ⟨by omega, hBm⟩)
  have := hAm.1
  omega

lemma sum_gap (k p : ℕ) (hkp : k < p) :
    ∑ j ∈ Finset.range (p - (k + 1) + 1), E (k + 1 + j) = ∑ j ∈ Finset.Ioc k p, E j := by
  have : Finset.Ioc k p = Finset.Ico (k + 1) (p + 1) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
  rw [this, Finset.sum_Ico_eq_sum_range, show p + 1 - (k + 1) = p - (k + 1) + 1 by omega]

lemma arrival_diff (k p : ℕ) (hkp : k < p) :
    arrival E k - arrival E p = (if k = 0 then E 0 else 0) + ∑ j ∈ Finset.Ioc k p, E j := by
  have hIcc : ∀ q, Finset.Icc 1 q = Finset.Ioc 0 q := fun q => by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  unfold arrival
  rw [if_neg (by omega : p ≠ 0)]
  split_ifs with hk
  · subst hk; rw [hIcc]; ring
  · rw [hIcc, hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le k) hkp.le]; ring

lemma edgeHat_eq (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) (k : ℕ) (i : Fin m) :
    edgeHat E R C k i = stepX (shiftS (k + 1) (fun k => (E k, R k, C k))) (R k) i -
      (if k = 0 then E 0 else 0) := by
  have hp := predJob_eq_srch (C := C) (E := E) hpred k i
  set T := srch (shiftS (k + 1) (fun k => (E k, R k, C k))) (R k i)
  have hlt := (predJob_spec hpred k i).1
  unfold edgeHat stepX
  have hz : shiftS (k + 1) (fun k => (E k, R k, C k)) T =
      (E (predJob R k i), R (predJob R k i), C (predJob R k i)) := by
    unfold shiftS; rw [hp]
  rw [hz, arrival_diff k (predJob R k i) hlt]
  have hpos : posS (R (predJob R k i)) (R k i) i = predPiece R k i := rfl
  simp only [hpos]
  have hs : ∑ j ∈ Finset.range (T + 1), (shiftS (k + 1) (fun k => (E k, R k, C k)) j).1 =
      ∑ j ∈ Finset.Ioc k (predJob R k i), E j := by
    rw [← sum_gap k (predJob R k i) hlt]
    rw [show predJob R k i - (k + 1) = T by omega]
    rfl
  rw [hs]
  ring

lemma pf_eq_cs (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) :
    ∀ (v : List (Fin m)) (k : ℕ), 1 ≤ k →
      pf E R C k v = cs (shiftS (k + 1) (fun k => (E k, R k, C k))) (R k) v := by
  intro v
  induction v with
  | nil => intro k _; simp [pf, cs]
  | cons i v ih =>
    intro k hk
    have hp := predJob_eq_srch (C := C) (E := E) hpred k i
    have hlt := (predJob_spec hpred k i).1
    simp only [pf, cs]
    rw [edgeHat_eq hpred, if_neg (by omega), sub_zero, ih (predJob R k i) (by omega)]
    set T := srch (shiftS (k + 1) (fun k => (E k, R k, C k))) (R k i)
    rw [shiftS_shiftS, show k + 1 + (T + 1) = predJob R k i + 1 by omega]
    have : (shiftS (k + 1) (fun k => (E k, R k, C k)) T).2.1 = R (predJob R k i) := by
      unfold shiftS; rw [hp]
    rw [this]

lemma pathSumHat_le_cs (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) (hE0 : 0 ≤ E 0)
    (v : List (Fin m)) :
    pathSumHat E R C v ≤ cs (shiftS 1 (fun k => (E k, R k, C k))) (R 0) v := by
  rw [pathSumHat_eq]
  cases v with
  | nil => simp [pf, cs]
  | cons i v =>
    have hp := predJob_eq_srch (C := C) (E := E) hpred 0 i
    have hlt := (predJob_spec hpred 0 i).1
    simp only [pf, cs]
    rw [edgeHat_eq hpred, if_pos rfl, pf_eq_cs hpred v (predJob R 0 i) (by omega)]
    simp only [zero_add] at hp ⊢
    set T := srch (shiftS 1 (fun k => (E k, R k, C k))) (R 0 i)
    rw [shiftS_shiftS, show 1 + (T + 1) = predJob R 0 i + 1 by omega]
    have : (shiftS 1 (fun k => (E k, R k, C k)) T).2.1 = R (predJob R 0 i) := by
      unfold shiftS; rw [hp]
    rw [this]
    linarith

end Rel

section CanonMeas

variable {m : ℕ}

lemma meas_coord (k : ℕ) : Measurable (fun z : ℕ → Tr m => z k) := measurable_pi_apply k

lemma meas_srch (s : ℕ) : Measurable (fun z : ℕ → Tr m => srch z s) := by
  unfold srch
  apply meas_sInf_nat
  intro k
  exact meas_countable_set ((meas_coord (m := m) k).snd.fst) {ρ | s ∈ Set.range ρ}

lemma meas_at {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℕ → Tr m} (hZ : Measurable Z)
    {K : Ω → ℕ} (hK : Measurable K) : Measurable (fun ω => Z ω (K ω)) :=
  meas_index hK (F := fun k ω => Z ω k) fun k => (meas_coord k).comp hZ

lemma meas_stepX_gen {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℕ → Tr m} (hZ : Measurable Z)
    (ρ : Fin m → ℕ) (i : Fin m) : Measurable (fun ω => stepX (Z ω) ρ i) := by
  unfold stepX
  have hT : Measurable (fun ω => srch (Z ω) (ρ i)) := (meas_srch (ρ i)).comp hZ
  have hzT : Measurable (fun ω => Z ω (srch (Z ω) (ρ i))) := meas_at hZ hT
  have hpos : Measurable (fun ω => posS (Z ω (srch (Z ω) (ρ i))).2.1 (ρ i) i) :=
    (measurable_of_countable (fun ρ' : Fin m → ℕ => posS ρ' (ρ i) i)).comp hzT.snd.fst
  have hc : Measurable (fun ω => (Z ω (srch (Z ω) (ρ i))).2.2
      (posS (Z ω (srch (Z ω) (ρ i))).2.1 (ρ i) i)) :=
    meas_index hpos (F := fun j ω => (Z ω (srch (Z ω) (ρ i))).2.2 j)
      fun j => (measurable_pi_apply j).comp hzT.snd.snd
  have hsum : Measurable (fun ω => ∑ k ∈ Finset.range (srch (Z ω) (ρ i) + 1), (Z ω k).1) :=
    meas_index hT (F := fun p ω => ∑ k ∈ Finset.range (p + 1), (Z ω k).1)
      fun p => Finset.measurable_sum _ fun k _ => ((meas_coord k).comp hZ).fst
  exact hc.sub hsum

lemma meas_shiftS_gen {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℕ → Tr m} (hZ : Measurable Z)
    {K : Ω → ℕ} (hK : Measurable K) : Measurable (fun ω => shiftS (K ω) (Z ω)) := by
  unfold shiftS
  exact measurable_pi_lambda _ fun j =>
    meas_index hK (F := fun p ω => Z ω (p + j)) fun p => (meas_coord (p + j)).comp hZ

lemma meas_cs : ∀ (v : List (Fin m)) (ρ : Fin m → ℕ), Measurable (fun z : ℕ → Tr m => cs z ρ v)
  | [], ρ => by simp only [cs]; exact measurable_const
  | i :: v, ρ => by
    simp only [cs]
    have hjoint : Measurable (fun q : (ℕ → Tr m) × (Fin m → ℕ) => cs q.1 q.2 v) :=
      meas_index measurable_snd (F := fun ρ' q => cs q.1 ρ' v)
        fun ρ' => (meas_cs v ρ').comp measurable_fst
    have hT : Measurable (fun z : ℕ → Tr m => srch z (ρ i)) := meas_srch (ρ i)
    refine (meas_stepX_gen measurable_id ρ i).add (hjoint.comp (Measurable.prodMk ?_ ?_))
    · exact meas_shiftS_gen measurable_id (hT.add_const 1)
    · exact (meas_at measurable_id hT).snd.fst

lemma meas_cs_joint (v : List (Fin m)) :
    Measurable (fun q : (ℕ → Tr m) × (Fin m → ℕ) => cs q.1 q.2 v) :=
  meas_index measurable_snd (F := fun ρ' q => cs q.1 ρ' v) fun ρ' => (meas_cs v ρ').comp measurable_fst

end CanonMeas

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma frequently_of_indep {β : Type*} [MeasurableSpace β] {X : ℕ → Ω → β}
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X P) {A : Set β} (hA : MeasurableSet A)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hlaw : ∀ k, P (X k ⁻¹' A) = c) :
    ∀ᵐ ω ∂P, ∃ᶠ k in atTop, X k ω ∈ A := by
  set s : ℕ → Set Ω := fun k => X k ⁻¹' A
  have hsm : ∀ k, MeasurableSet (s k) := fun k => hX k hA
  have hs : iIndepSet s P := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro S
    exact hind.measure_inter_preimage_eq_mul S (sets := fun _ => A) (fun _ _ => hA)
  have hsum : (∑' k, P (s k)) = ∞ := by
    simp only [s, hlaw]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hc
  have h1 := measure_limsup_eq_one hsm hs hsum
  have hmeas : MeasurableSet (limsup s atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => MeasurableSet.iUnion
      fun _ => hsm i
  have h2 : ∀ᵐ ω ∂P, ω ∈ limsup s atTop := by
    rw [ae_iff]
    have := prob_compl_eq_zero_iff hmeas (μ := P)
    rw [← this.2 h1]
    rfl
  filter_upwards [h2] with ω hω
  exact Filter.mem_limsup_iff_frequently_mem.1 hω


lemma expM_Iic_zero {r : ℝ} (hr : 0 < r) : expMeasure r (Set.Iic 0) = 0 := by
  haveI := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr 0
  rw [cdf_eq_real] at h
  simp only [le_refl, if_true, mul_zero, neg_zero, Real.exp_zero, sub_self] at h
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

lemma expM_Ioi_one {r : ℝ} (hr : 0 < r) : expMeasure r (Set.Ioi 1) ≠ 0 := by
  haveI := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr 1
  rw [cdf_eq_real] at h
  simp only [zero_le_one, if_true, mul_one] at h
  intro h0
  have hc : expMeasure r (Set.Iic 1)ᶜ = 0 := by rw [Set.compl_Iic]; exact h0
  rw [prob_compl_eq_one_sub measurableSet_Iic, tsub_eq_zero_iff_le] at hc
  have h1 : expMeasure r (Set.Iic 1) = 1 := le_antisymm prob_le_one hc
  rw [measureReal_def, h1, ENNReal.toReal_one] at h
  have : 0 < Real.exp (-r) := Real.exp_pos _
  linarith

/-- the support of `uniformInj m n` -/
def injSet (m n : ℕ) : Set (Fin m → ℕ) := {ρ | Function.Injective ρ ∧ ∀ i, ρ i < n}

lemma injSet_finite (m n : ℕ) : (injSet m n).Finite := by
  refine Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin m => Set.Iio n)
    (fun _ => Set.finite_Iio n)) ?_
  intro ρ hρ
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iio, forall_const]
  exact hρ.2

lemma swap_mem {m n : ℕ} (hm : 0 < m) (hn : m ≤ n) {s0 : ℕ} (hs0 : s0 < n) :
    (fun i : Fin m => Equiv.swap 0 s0 i.val) ∈ injSet m n ∩ {ρ | s0 ∈ Set.range ρ} := by
  refine ⟨⟨fun i j h => Fin.ext ((Equiv.swap 0 s0).injective h), fun i => ?_⟩,
    ⟨⟨0, hm⟩, by simp⟩⟩
  show Equiv.swap 0 s0 i.val < n
  rcases eq_or_ne i.val 0 with h0 | h0
  · simp [h0, hs0]
  · rcases eq_or_ne i.val s0 with h1 | h1
    · rw [h1, Equiv.swap_apply_right]; omega
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]; omega

lemma uniformInj_eq {m n : ℕ} : uniformInj m n = uniformOn (injSet m n) := rfl

lemma uniformInj_prob {m n : ℕ} (hm : 0 < m) (hn : m ≤ n) : IsProbabilityMeasure (uniformInj m n) := by
  constructor
  rw [uniformInj_eq]
  exact uniformOn_of_univ (injSet_finite m n) ⟨_, (swap_mem hm hn (lt_of_lt_of_le hm hn)).1⟩

variable {m n : ℕ} {lam : ℝ} {Bm : Measure (Fin m → ℝ)} [IsProbabilityMeasure Bm]
  {E : ℕ → Ω → ℝ} {R : ℕ → Ω → (Fin m → ℕ)} {C : ℕ → Ω → (Fin m → ℝ)}

lemma prob_triple (hsys : IsSyncSystem P m n lam Bm E R C) (k : ℕ)
    {A : Set ℝ} {B : Set (Fin m → ℕ)} {D : Set (Fin m → ℝ)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hD : MeasurableSet D) :
    P ((fun ω => (E k ω, R k ω, C k ω)) ⁻¹' (A ×ˢ (B ×ˢ D))) =
      expMeasure (lam * n) A * (uniformInj m n B * Bm D) := by
  have hT : Measurable (fun ω => (E k ω, R k ω, C k ω)) :=
    (hsys.1 k).1.prodMk ((hsys.1 k).2.1.prodMk (hsys.1 k).2.2)
  rw [← Measure.map_apply hT (hA.prod (hB.prod hD)), hsys.2.2 k, Measure.prod_prod,
    Measure.prod_prod]

lemma ae_good (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam)
    (hsys : IsSyncSystem P m n lam Bm E R C) :
    ∀ᵐ ω ∂P, (∀ k, 0 < E k ω) ∧ (∃ᶠ k in atTop, 1 < E k ω) ∧ (∀ k, R k ω ∈ injSet m n) ∧
      (∀ s0 : ℕ, s0 < n → ∃ᶠ k in atTop, s0 ∈ Set.range (R k ω)) := by
  have hr : 0 < lam * n := mul_pos hlam (by exact_mod_cast lt_of_lt_of_le hm hn)
  haveI := isProbabilityMeasure_expMeasure hr
  haveI := uniformInj_prob hm hn
  set T : ℕ → Ω → ℝ × (Fin m → ℕ) × (Fin m → ℝ) := fun k ω => (E k ω, R k ω, C k ω)
  have hT : ∀ k, Measurable (T k) := fun k =>
    (hsys.1 k).1.prodMk ((hsys.1 k).2.1.prodMk (hsys.1 k).2.2)
  have hdisc : ∀ B : Set (Fin m → ℕ), MeasurableSet B := fun B => B.to_countable.measurableSet
  refine (ae_all_iff.2 fun k => ?_).and ((?_ : ∀ᵐ ω ∂P, ∃ᶠ k in atTop, 1 < E k ω).and
    ((ae_all_iff.2 fun k => ?_).and ?_))
  · -- positivity of the gaps
    have h0 : P ((fun ω => (E k ω, R k ω, C k ω)) ⁻¹' (Set.Iic 0 ×ˢ (Set.univ ×ˢ Set.univ))) = 0 := by
      rw [prob_triple hsys k measurableSet_Iic MeasurableSet.univ MeasurableSet.univ,
        expM_Iic_zero hr, zero_mul]
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [Set.mem_setOf_eq, not_lt] at hω
    simp [hω]
  · refine frequently_of_indep (X := T) hT hsys.2.1 (A := Set.Ioi 1 ×ˢ (Set.univ ×ˢ Set.univ))
      (measurableSet_Ioi.prod (MeasurableSet.univ.prod MeasurableSet.univ))
      (c := expMeasure (lam * n) (Set.Ioi 1)) (expM_Ioi_one hr) (fun k => ?_) |>.mono ?_
    · rw [prob_triple hsys k measurableSet_Ioi MeasurableSet.univ MeasurableSet.univ]
      simp
    · intro ω hω
      exact hω.mono fun k hk => by simpa [T] using hk
  · -- routing in the support
    have h0 : P ((fun ω => (E k ω, R k ω, C k ω)) ⁻¹'
        (Set.univ ×ˢ ((injSet m n)ᶜ ×ˢ Set.univ))) = 0 := by
      rw [prob_triple hsys k MeasurableSet.univ (hdisc _) MeasurableSet.univ, uniformInj_eq,
        (uniformOn_eq_zero_iff (injSet_finite m n)).2 (Set.inter_compl_self _)]
      simp
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simpa using hω
  · -- every server is used infinitely often
    have hcount : ∀ s0 : ℕ, s0 < n → ∀ᵐ ω ∂P, ∃ᶠ k in atTop, s0 ∈ Set.range (R k ω) := by
      intro s0 hs0
      have hne : uniformInj m n {ρ | s0 ∈ Set.range ρ} ≠ 0 := by
        rw [uniformInj_eq, Ne, uniformOn_eq_zero_iff (injSet_finite m n)]
        exact Set.nonempty_iff_ne_empty.1 ⟨_, swap_mem hm hn hs0⟩
      refine frequently_of_indep (X := T) hT hsys.2.1
        (A := Set.univ ×ˢ ({ρ | s0 ∈ Set.range ρ} ×ˢ Set.univ))
        (MeasurableSet.univ.prod ((hdisc _).prod MeasurableSet.univ))
        (c := uniformInj m n {ρ | s0 ∈ Set.range ρ}) hne (fun k => ?_) |>.mono ?_
      · rw [prob_triple hsys k MeasurableSet.univ (hdisc _) MeasurableSet.univ]
        simp
      · intro ω hω
        exact hω.mono fun k hk => by simpa [T] using hk
    refine ae_all_iff.2 fun s0 => ?_
    by_cases h : s0 < n
    · filter_upwards [hcount s0 h] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' h

end Prob


section Unif

variable {m n : ℕ}

lemma swapComp_mem {s s' : ℕ} (hs : s < n) (hs' : s' < n) {ρ : Fin m → ℕ} (hρ : ρ ∈ injSet m n) :
    (fun j => Equiv.swap s s' (ρ j)) ∈ injSet m n := by
  refine ⟨fun a b h => hρ.1 ((Equiv.swap s s').injective h), fun j => ?_⟩
  have := hρ.2 j
  show Equiv.swap s s' (ρ j) < n
  rcases eq_or_ne (ρ j) s with h1 | h1
  · rw [h1, Equiv.swap_apply_left]; exact hs'
  · rcases eq_or_ne (ρ j) s' with h2 | h2
    · rw [h2, Equiv.swap_apply_right]; exact hs
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact this

lemma uniformInj_apply (t : Set (Fin m → ℕ)) :
    uniformInj m n t = (Measure.count (injSet m n))⁻¹ * Measure.count (injSet m n ∩ t) := by
  rw [uniformInj_eq, uniformOn, cond_apply (injSet_finite m n).measurableSet]

lemma uniformInj_coord_eq (i : Fin m) {s s' : ℕ} (hs : s < n) (hs' : s' < n) :
    uniformInj m n {ρ | ρ i = s} = uniformInj m n {ρ | ρ i = s'} := by
  rw [uniformInj_apply, uniformInj_apply]
  congr 1
  set f : (Fin m → ℕ) → (Fin m → ℕ) := fun ρ j => Equiv.swap s s' (ρ j)
  have hf : Function.Injective f := by
    intro a b h
    funext j
    exact (Equiv.swap s s').injective (congrFun h j)
  have himg : f '' (injSet m n ∩ {ρ | ρ i = s}) = injSet m n ∩ {ρ | ρ i = s'} := by
    ext ρ
    constructor
    · rintro ⟨ρ0, ⟨h1, h2⟩, rfl⟩
      refine ⟨swapComp_mem hs hs' h1, ?_⟩
      simp only [Set.mem_setOf_eq, f] at h2 ⊢
      rw [h2, Equiv.swap_apply_left]
    · rintro ⟨h1, h2⟩
      refine ⟨f ρ, ⟨swapComp_mem hs hs' h1, ?_⟩, ?_⟩
      · simp only [Set.mem_setOf_eq, f] at h2 ⊢
        rw [h2, Equiv.swap_apply_right]
      · funext j; simp [f]
  have hm : ∀ t : Set (Fin m → ℕ), MeasurableSet t := fun t => t.to_countable.measurableSet
  rw [Measure.count_apply (hm _), Measure.count_apply (hm _), ← himg,
    hf.injOn.encard_image]

lemma uniformInj_coord (hm : 0 < m) (hn : m ≤ n) (i : Fin m) {s : ℕ} (hs : s < n) :
    uniformInj m n {ρ | ρ i = s} = (n : ℝ≥0∞)⁻¹ := by
  haveI := uniformInj_prob hm hn
  have hall : ∀ s' ∈ Finset.range n, uniformInj m n {ρ | ρ i = s'} = uniformInj m n {ρ | ρ i = s} :=
    fun s' hs' => uniformInj_coord_eq i (Finset.mem_range.1 hs') hs
  have hm' : ∀ t : Set (Fin m → ℕ), MeasurableSet t := fun t => t.to_countable.measurableSet
  have hsum : ∑ s' ∈ Finset.range n, uniformInj m n {ρ | ρ i = s'} = 1 := by
    rw [← measure_biUnion_finset]
    · apply le_antisymm prob_le_one
      have hsub : injSet m n ⊆ ⋃ s' ∈ Finset.range n, {ρ : Fin m → ℕ | ρ i = s'} := by
        intro ρ hρ
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range]
        exact ⟨ρ i, hρ.2 i, rfl⟩
      calc (1 : ℝ≥0∞) = uniformInj m n (injSet m n) := by
            rw [uniformInj_eq]
            exact (uniformOn_self (injSet_finite m n) ⟨_, (swap_mem hm hn (lt_of_lt_of_le hm hn)).1⟩).symm
        _ ≤ _ := measure_mono hsub
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      intro ρ h1 h2
      exact hab (h1.symm.trans h2)
    · intro b _; exact hm' _
  rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)

lemma posS_of_inj {ρ : Fin m → ℕ} (hρ : Function.Injective ρ) {s : ℕ} {i fb : Fin m} (h : ρ i = s) :
    posS ρ s fb = i := by
  unfold posS
  have hex : ∃ j, ρ j = s := ⟨i, h⟩
  rw [dif_pos hex]
  exact hρ (hex.choose_spec.trans h.symm)

lemma uniformInj_mem_range (hm : 0 < m) (hn : m ≤ n) {s : ℕ} (hs : s < n) :
    uniformInj m n {ρ | s ∈ Set.range ρ} = (m : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by
  have hm' : ∀ t : Set (Fin m → ℕ), MeasurableSet t := fun t => t.to_countable.measurableSet
  have h1 : uniformInj m n {ρ | s ∈ Set.range ρ} =
      uniformInj m n (⋃ i : Fin m, (injSet m n ∩ {ρ | ρ i = s})) := by
    rw [← Set.inter_iUnion, uniformInj_eq, uniformOn_inter_self (injSet_finite m n)]
    congr 1
    ext ρ; simp [eq_comm]
  rw [h1, measure_iUnion]
  · have : ∀ i : Fin m, uniformInj m n (injSet m n ∩ {ρ | ρ i = s}) = (n : ℝ≥0∞)⁻¹ := by
      intro i
      rw [uniformInj_eq, uniformOn_inter_self (injSet_finite m n), ← uniformInj_eq]
      exact uniformInj_coord hm hn i hs
    simp only [this, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  · intro a b hab
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro ρ ⟨hρ, h1⟩ ⟨-, h2⟩
    exact hab (hρ.1 (h1.trans h2.symm))
  · intro i; exact hm' _

end Unif

lemma meas_expPDF (r : ℝ) : Measurable (exponentialPDF r) :=
  (measurable_exponentialPDFReal r).ennreal_ofReal

lemma lintegral_exp_neg_expMeasure {r β : ℝ} (hr : 0 < r) (hβ : 0 < β) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (-(β * t))) ∂(expMeasure r) = ENNReal.ofReal (r / (r + β)) := by
  have hrb : 0 < r + β := by linarith
  have h1 : (expMeasure r) = volume.withDensity (exponentialPDF r) := rfl
  rw [h1, lintegral_withDensity_eq_lintegral_mul _ (meas_expPDF r)
    (by fun_prop)]
  have key : ∀ t, (exponentialPDF r * fun t => ENNReal.ofReal (Real.exp (-(β * t)))) t =
      ENNReal.ofReal (r / (r + β)) * exponentialPDF (r + β) t := by
    intro t
    simp only [Pi.mul_apply]
    rcases lt_or_ge t 0 with ht | ht
    · rw [exponentialPDF_of_neg ht, exponentialPDF_of_neg ht]; simp
    · rw [exponentialPDF_of_nonneg ht, exponentialPDF_of_nonneg ht,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : Real.exp (-((r + β) * t)) = Real.exp (-(r * t)) * Real.exp (-(β * t)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; field_simp
  simp_rw [key]
  rw [lintegral_const_mul _ (meas_expPDF _), lintegral_exponentialPDF_eq_one hrb,
    mul_one]



section Base

variable {m n : ℕ} {lam : ℝ} {Bm : Measure (Fin m → ℝ)} [IsProbabilityMeasure Bm]

/-- the law of one job triple -/
noncomputable def muT (m n : ℕ) (lam : ℝ) (Bm : Measure (Fin m → ℝ)) : Measure (Tr m) :=
  (expMeasure (lam * n)).prod ((uniformInj m n).prod Bm)

noncomputable def fA (β : ℝ) (s : ℕ) (t : Tr m) : ℝ≥0∞ :=
  (if s ∈ Set.range t.2.1 then 0 else 1) * ENNReal.ofReal (Real.exp (-(β * t.1)))

noncomputable def fB (β : ℝ) (s : ℕ) (fb : Fin m) (t : Tr m) : ℝ≥0∞ :=
  (if s ∈ Set.range t.2.1 then 1 else 0) * ENNReal.ofReal (Real.exp (-(β * t.1))) *
    ENNReal.ofReal (Real.exp (β * t.2.2 (posS t.2.1 s fb)))

lemma meas_fA (β : ℝ) (s : ℕ) : Measurable (fA (m := m) β s) := by
  unfold fA
  refine Measurable.mul ?_ (by fun_prop)
  exact (measurable_of_countable (fun ρ : Fin m → ℕ => if s ∈ Set.range ρ then (0 : ℝ≥0∞) else 1)).comp
    measurable_snd.fst

lemma meas_fB (β : ℝ) (s : ℕ) (fb : Fin m) : Measurable (fB (m := m) β s fb) := by
  unfold fB
  refine Measurable.mul (Measurable.mul ?_ (by fun_prop)) ?_
  · exact (measurable_of_countable (fun ρ : Fin m → ℕ => if s ∈ Set.range ρ then (1 : ℝ≥0∞) else 0)).comp
      measurable_snd.fst
  · refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.const_mul ?_ β))
    exact meas_index ((measurable_of_countable (fun ρ : Fin m → ℕ => posS ρ s fb)).comp
      measurable_snd.fst) (F := fun j (t : Tr m) => t.2.2 j)
      fun j => (measurable_pi_apply j).comp measurable_snd.snd

lemma ae_inj (hm : 0 < m) (hn : m ≤ n) : ∀ᵐ ρ ∂(uniformInj m n), ρ ∈ injSet m n := by
  rw [ae_iff]
  have : uniformInj m n (injSet m n)ᶜ = 0 := by
    rw [uniformInj_eq, (uniformOn_eq_zero_iff (injSet_finite m n)).2 (Set.inter_compl_self _)]
  exact this

lemma int_fA (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam) {β : ℝ} (hβ : 0 < β) {s : ℕ} (hs : s < n) :
    ∫⁻ t, fA β s t ∂(muT m n lam Bm) =
      ENNReal.ofReal (lam * n / (lam * n + β)) * (1 - (m : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) := by
  haveI := uniformInj_prob hm hn
  have hr : 0 < lam * n := mul_pos hlam (by exact_mod_cast lt_of_lt_of_le hm hn)
  unfold muT fA
  have hmeas : Measurable (fun ρ : Fin m → ℕ => if s ∈ Set.range ρ then (0 : ℝ≥0∞) else 1) :=
    measurable_of_countable _
  rw [show (fun t : Tr m => (if s ∈ Set.range t.2.1 then (0 : ℝ≥0∞) else 1) *
      ENNReal.ofReal (Real.exp (-(β * t.1)))) = fun t => ENNReal.ofReal (Real.exp (-(β * t.1))) *
      ((fun q : (Fin m → ℕ) × (Fin m → ℝ) => (if s ∈ Set.range q.1 then (0 : ℝ≥0∞) else 1) * 1) t.2)
      from by funext t; simp [mul_comm]]
  rw [lintegral_prod_mul (f := fun e => ENNReal.ofReal (Real.exp (-(β * e))))
    (g := fun q : (Fin m → ℕ) × (Fin m → ℝ) => (if s ∈ Set.range q.1 then (0 : ℝ≥0∞) else 1) * 1)
    (by fun_prop) ((hmeas.comp measurable_fst).mul measurable_const).aemeasurable,
    lintegral_exp_neg_expMeasure hr hβ]
  congr 1
  rw [lintegral_prod_mul (f := fun ρ : Fin m → ℕ => if s ∈ Set.range ρ then (0 : ℝ≥0∞) else 1)
    (g := fun _ => (1 : ℝ≥0∞)) hmeas.aemeasurable aemeasurable_const]
  simp only [lintegral_const, measure_univ, mul_one]
  have hind : (fun ρ : Fin m → ℕ => if s ∈ Set.range ρ then (0 : ℝ≥0∞) else 1) =
      Set.indicator ({ρ | s ∈ Set.range ρ}ᶜ) (1 : (Fin m → ℕ) → ℝ≥0∞) := by
    funext ρ; unfold Set.indicator; by_cases h : s ∈ Set.range ρ <;> simp_all
  rw [hind, lintegral_indicator_one (Set.to_countable _).measurableSet,
    prob_compl_eq_one_sub (Set.to_countable _).measurableSet, uniformInj_mem_range hm hn hs]

lemma int_fB (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam) {β : ℝ} (hβ : 0 < β) {s : ℕ} (hs : s < n)
    (fb : Fin m) :
    ∫⁻ t, fB β s fb t ∂(muT m n lam Bm) =
      ENNReal.ofReal (lam * n / (lam * n + β)) *
        ((n : ℝ≥0∞)⁻¹ * ∑ j : Fin m, ∫⁻ c, ENNReal.ofReal (Real.exp (β * c j)) ∂Bm) := by
  haveI := uniformInj_prob hm hn
  have hr : 0 < lam * n := mul_pos hlam (by exact_mod_cast lt_of_lt_of_le hm hn)
  set M : Fin m → ℝ≥0∞ := fun j => ∫⁻ c, ENNReal.ofReal (Real.exp (β * c j)) ∂Bm
  have hpos : Measurable (fun ρ : Fin m → ℕ => posS ρ s fb) := measurable_of_countable _
  have hG : Measurable (fun q : (Fin m → ℕ) × (Fin m → ℝ) =>
      (if s ∈ Set.range q.1 then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (Real.exp (β * q.2 (posS q.1 s fb)))) := by
    refine Measurable.mul ((measurable_of_countable (fun ρ : Fin m → ℕ =>
      if s ∈ Set.range ρ then (1 : ℝ≥0∞) else 0)).comp measurable_fst) ?_
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.const_mul ?_ β))
    exact meas_index (hpos.comp measurable_fst) (F := fun j (q : (Fin m → ℕ) × (Fin m → ℝ)) => q.2 j)
      fun j => (measurable_pi_apply j).comp measurable_snd
  unfold muT fB
  rw [show (fun t : Tr m => (if s ∈ Set.range t.2.1 then (1 : ℝ≥0∞) else 0) *
      ENNReal.ofReal (Real.exp (-(β * t.1))) * ENNReal.ofReal (Real.exp (β * t.2.2 (posS t.2.1 s fb))))
      = fun t => ENNReal.ofReal (Real.exp (-(β * t.1))) *
        ((fun q : (Fin m → ℕ) × (Fin m → ℝ) => (if s ∈ Set.range q.1 then (1 : ℝ≥0∞) else 0) *
          ENNReal.ofReal (Real.exp (β * q.2 (posS q.1 s fb)))) t.2) from by funext t; ring]
  rw [lintegral_prod_mul (f := fun e => ENNReal.ofReal (Real.exp (-(β * e)))) (by fun_prop)
    hG.aemeasurable, lintegral_exp_neg_expMeasure hr hβ]
  congr 1
  rw [lintegral_prod _ hG.aemeasurable]
  have hinner : ∀ ρ : Fin m → ℕ, ∫⁻ c, (if s ∈ Set.range ρ then (1 : ℝ≥0∞) else 0) *
      ENNReal.ofReal (Real.exp (β * c (posS ρ s fb))) ∂Bm =
      (if s ∈ Set.range ρ then (1 : ℝ≥0∞) else 0) * M (posS ρ s fb) := by
    intro ρ
    rw [lintegral_const_mul _ (by fun_prop)]
  simp only [hinner]
  have hae : ∀ᵐ ρ ∂(uniformInj m n), (if s ∈ Set.range ρ then (1 : ℝ≥0∞) else 0) * M (posS ρ s fb) =
      ∑ j : Fin m, Set.indicator {ρ : Fin m → ℕ | ρ j = s} (fun _ => M j) ρ := by
    filter_upwards [ae_inj hm hn] with ρ hρ
    by_cases h : s ∈ Set.range ρ
    · obtain ⟨j, hj⟩ := h
      rw [if_pos ⟨j, hj⟩, one_mul, posS_of_inj hρ.1 hj,
        Finset.sum_eq_single j]
      · simp [hj]
      · intro b _ hb
        simp only [Set.indicator, Set.mem_setOf_eq]
        rw [if_neg]
        intro hb'
        exact hb (hρ.1 (hb'.trans hj.symm))
      · simp
    · rw [if_neg h, zero_mul]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [Set.indicator, Set.mem_setOf_eq]
      rw [if_neg]
      intro hj
      exact h ⟨j, hj⟩
  rw [lintegral_congr_ae hae, lintegral_finset_sum _ (fun j _ =>
    (measurable_of_countable _))]
  simp only [lintegral_indicator_const ((Set.to_countable _).measurableSet),
    uniformInj_coord hm hn _ hs]
  rw [Finset.mul_sum]
  congr 1; ext j; ring

lemma pieceLaw_lintegral (hm : 0 < m) (β : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(pieceLaw Bm) =
      (m : ℝ≥0∞)⁻¹ * ∑ j : Fin m, ∫⁻ c, ENNReal.ofReal (Real.exp (β * c j)) ∂Bm := by
  unfold pieceLaw
  rw [lintegral_smul_measure, lintegral_finset_sum_measure]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_map (by fun_prop) (measurable_pi_apply j)]

/-- the geometric series of first-passage contributions -/
lemma geom_bound (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam) {β : ℝ} (hβ : 0 < β) {s : ℕ}
    (hs : s < n) (fb : Fin m) :
    ∑' p : ℕ, (∫⁻ t, fA β s t ∂(muT m n lam Bm)) ^ p * ∫⁻ t, fB β s fb t ∂(muT m n lam Bm) ≤
      (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(pieceLaw Bm)) *
        ENNReal.ofReal (lam * m / (lam * m + β)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le hm hn
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn : (m : ℝ) / n ≤ 1 := (div_le_one hnpos).2 (by exact_mod_cast hn)
  set L : ℝ := lam * n / (lam * n + β) with hL
  have hL0 : 0 ≤ L := by positivity
  have hL1 : L < 1 := by rw [hL, div_lt_one (by positivity)]; linarith
  have hx : (m : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((m : ℝ) / n) := by
    rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]
  have hsumM : (n : ℝ≥0∞)⁻¹ * ∑ j : Fin m, ∫⁻ c, ENNReal.ofReal (Real.exp (β * c j)) ∂Bm =
      ENNReal.ofReal ((m : ℝ) / n) * ∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(pieceLaw Bm) := by
    rw [pieceLaw_lintegral hm, ← hx]
    have h0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
    have htop : (m : ℝ≥0∞) ≠ ⊤ := by simp
    calc (n : ℝ≥0∞)⁻¹ * ∑ j : Fin m, ∫⁻ c, ENNReal.ofReal (Real.exp (β * c j)) ∂Bm
        = (n : ℝ≥0∞)⁻¹ * (((m : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹) *
            ∑ j : Fin m, ∫⁻ c, ENNReal.ofReal (Real.exp (β * c j)) ∂Bm) := by
          rw [ENNReal.mul_inv_cancel h0 htop, one_mul]
      _ = _ := by ring
  set Mbar := ∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(pieceLaw Bm)
  rw [int_fA hm hn hlam hβ hs, int_fB hm hn hlam hβ hs fb, hsumM, ENNReal.tsum_mul_right,
    ENNReal.tsum_geometric, hx]
  have h1 : 1 - ENNReal.ofReal ((m : ℝ) / n) = ENNReal.ofReal (1 - (m : ℝ) / n) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  have hq0 : 0 ≤ 1 - (m : ℝ) / n := by linarith
  have h2 : 1 - ENNReal.ofReal L * ENNReal.ofReal (1 - (m : ℝ) / n) =
      ENNReal.ofReal (1 - L * (1 - (m : ℝ) / n)) := by
    rw [← ENNReal.ofReal_mul hL0, ENNReal.ofReal_sub _ (mul_nonneg hL0 hq0)]
    simp
  have hpos : 0 < 1 - L * (1 - (m : ℝ) / n) := by
    have : L * (1 - (m : ℝ) / n) ≤ L :=
      mul_le_of_le_one_right hL0 (by have h' : (0 : ℝ) ≤ (m : ℝ) / n := (by positivity); linarith)
    linarith
  rw [h1, h2, ← ENNReal.ofReal_inv_of_pos hpos]
  have hb : 0 < lam * n + β := by positivity
  have hb2 : 0 < lam * m + β := by positivity
  have hc : (1 - L * (1 - (m : ℝ) / n))⁻¹ * (L * ((m : ℝ) / n)) = lam * m / (lam * m + β) := by
    have h1' : 1 - L * (1 - (m : ℝ) / n) = (lam * m + β) / (lam * n + β) := by
      rw [hL]; field_simp; ring
    rw [h1', hL]
    field_simp
  apply le_of_eq
  calc ENNReal.ofReal (1 - L * (1 - (m : ℝ) / n))⁻¹ * (ENNReal.ofReal L * (ENNReal.ofReal ((m : ℝ) / n) * Mbar))
      = ENNReal.ofReal ((1 - L * (1 - (m : ℝ) / n))⁻¹ * (L * ((m : ℝ) / n))) * Mbar := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hL0]; ring
    _ = Mbar * ENNReal.ofReal (lam * m / (lam * m + β)) := by rw [hc, mul_comm]

end Base

section Iid

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma block_indep {β : Type*} [MeasurableSpace β] {ζ : ℕ → Ω → β} (hζ : ∀ k, Measurable (ζ k))
    (hind : iIndepFun ζ P) (p : ℕ) :
    IndepFun (fun ω k => ζ (min k p) ω) (fun ω k => ζ (p + 1 + k) ω) P := by
  rw [iIndepFun_iff_iIndep] at hind
  have h := indep_iSup_of_disjoint (fun k => (hζ k).comap_le) hind
    (S := {k | k ≤ p}) (T := {k | p < k}) (by
      rw [Set.disjoint_left]; intro k h1 h2; simp only [Set.mem_setOf_eq] at h1 h2; omega)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun k => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun i (_ : i ∈ {k | k ≤ p}) =>
      MeasurableSpace.comap (ζ i) inferInstance) (min k p) (min_le_right k p)
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun k => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun i (_ : i ∈ {k | p < k}) =>
      MeasurableSpace.comap (ζ i) inferInstance) (p + 1 + k) (by show p < p + 1 + k; omega)

lemma indep_fubini {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {Y : Ω → α} {Z : Ω → β}
    (hY : Measurable Y) (hZ : Measurable Z) (hind : IndepFun Y Z P) {H : α × β → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ ω, H (Y ω, Z ω) ∂P = ∫⁻ y, ∫⁻ z, H (y, z) ∂(P.map Z) ∂(P.map Y) := by
  rw [← lintegral_map hH (hY.prodMk hZ),
    (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).1 hind,
    lintegral_prod _ hH.aemeasurable]

variable {m n : ℕ} {lam : ℝ} {Bm : Measure (Fin m → ℝ)} [IsProbabilityMeasure Bm]

/-- an i.i.d. sequence of job triples with law `muT` -/
structure IsIid (P : Measure Ω) (m n : ℕ) (lam : ℝ) (Bm : Measure (Fin m → ℝ)) (ζ : ℕ → Ω → Tr m) :
    Prop where
  meas : ∀ k, Measurable (ζ k)
  indep : iIndepFun ζ P
  law : ∀ k, P.map (ζ k) = muT m n lam Bm

lemma IsIid.tail {ζ : ℕ → Ω → Tr m} (h : IsIid P m n lam Bm ζ) (p : ℕ) :
    IsIid P m n lam Bm (fun k => ζ (p + 1 + k)) where
  meas k := h.meas _
  indep := h.indep.precomp (g := fun k => p + 1 + k) (fun a b hab => by simpa using hab)
  law k := h.law _

lemma prob_muT (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam) {A : Set ℝ} {B : Set (Fin m → ℕ)}
    {D : Set (Fin m → ℝ)} (hA : MeasurableSet A) (hD : MeasurableSet D) :
    muT m n lam Bm (A ×ˢ (B ×ˢ D)) = expMeasure (lam * n) A * (uniformInj m n B * Bm D) := by
  unfold muT
  rw [Measure.prod_prod, Measure.prod_prod]

lemma IsIid.ae_inj (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam) {ζ : ℕ → Ω → Tr m}
    (h : IsIid P m n lam Bm ζ) : ∀ᵐ ω ∂P, ∀ k, (ζ k ω).2.1 ∈ injSet m n := by
  refine ae_all_iff.2 fun k => ?_
  have hdisc : ∀ B : Set (Fin m → ℕ), MeasurableSet B := fun B => B.to_countable.measurableSet
  have h0 : P (ζ k ⁻¹' (Set.univ ×ˢ ((injSet m n)ᶜ ×ˢ Set.univ))) = 0 := by
    rw [← Measure.map_apply (h.meas k) (MeasurableSet.univ.prod ((hdisc _).prod MeasurableSet.univ)),
      h.law k, prob_muT hm hn hlam MeasurableSet.univ MeasurableSet.univ, uniformInj_eq,
      (uniformOn_eq_zero_iff (injSet_finite m n)).2 (Set.inter_compl_self _)]
    simp
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h0
  simpa using hω

lemma IsIid.ae_appears (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam) {ζ : ℕ → Ω → Tr m}
    (h : IsIid P m n lam Bm ζ) {s : ℕ} (hs : s < n) :
    ∀ᵐ ω ∂P, ∃ k, s ∈ Set.range (ζ k ω).2.1 := by
  have hr : 0 < lam * n := mul_pos hlam (by exact_mod_cast lt_of_lt_of_le hm hn)
  haveI := isProbabilityMeasure_expMeasure hr
  have hdisc : ∀ B : Set (Fin m → ℕ), MeasurableSet B := fun B => B.to_countable.measurableSet
  have hne : uniformInj m n {ρ | s ∈ Set.range ρ} ≠ 0 := by
    rw [uniformInj_eq, Ne, uniformOn_eq_zero_iff (injSet_finite m n)]
    exact Set.nonempty_iff_ne_empty.1 ⟨_, swap_mem hm hn hs⟩
  have := frequently_of_indep (X := ζ) h.meas h.indep
    (A := Set.univ ×ˢ ({ρ | s ∈ Set.range ρ} ×ˢ Set.univ))
    (MeasurableSet.univ.prod ((hdisc _).prod MeasurableSet.univ))
    (c := uniformInj m n {ρ | s ∈ Set.range ρ}) hne (fun k => by
      rw [← Measure.map_apply (h.meas k) (MeasurableSet.univ.prod ((hdisc _).prod MeasurableSet.univ)),
        h.law k, prob_muT hm hn hlam MeasurableSet.univ MeasurableSet.univ]
      simp)
  filter_upwards [this] with ω hω
  obtain ⟨k, hk⟩ := hω.exists
  exact ⟨k, by simpa using hk⟩

end Iid

section Core

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m n : ℕ} {lam : ℝ} {Bm : Measure (Fin m → ℝ)} [IsProbabilityMeasure Bm]

/-- indicator that the first occurrence of server `s` is at position `p` -/
noncomputable def Aind (p s : ℕ) (z : ℕ → Tr m) : ℝ≥0∞ :=
  if s ∈ Set.range (z p).2.1 ∧ ∀ k < p, s ∉ Set.range (z k).2.1 then 1 else 0

noncomputable def Xp (p s : ℕ) (fb : Fin m) (z : ℕ → Tr m) : ℝ :=
  (z p).2.2 (posS (z p).2.1 s fb) - ∑ k ∈ Finset.range (p + 1), (z k).1

lemma meas_Aind (p s : ℕ) : Measurable (Aind (m := m) p s) := by
  unfold Aind
  have : (fun z : ℕ → Tr m => if s ∈ Set.range (z p).2.1 ∧ ∀ k < p, s ∉ Set.range (z k).2.1
      then (1 : ℝ≥0∞) else 0) = (fun ρs : Fin (p + 1) → (Fin m → ℕ) =>
        if s ∈ Set.range (ρs (Fin.last p)) ∧ ∀ k : Fin (p + 1), k < Fin.last p → s ∉ Set.range (ρs k)
        then (1 : ℝ≥0∞) else 0) ∘ (fun z (k : Fin (p + 1)) => (z k).2.1) := by
    funext z
    simp only [Function.comp_apply, Fin.val_last]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun k hk => h2 k (by simpa [Fin.lt_def] using hk)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun k hk => h2 ⟨k, by omega⟩ (by simp [Fin.lt_def]; omega)⟩
  rw [this]
  exact (measurable_of_countable _).comp (measurable_pi_lambda _ fun k =>
    ((meas_coord (m := m) k).snd.fst))

lemma meas_Xp (p s : ℕ) (fb : Fin m) : Measurable (Xp (m := m) p s fb) := by
  unfold Xp
  have hpos : Measurable (fun z : ℕ → Tr m => posS (z p).2.1 s fb) :=
    (measurable_of_countable (fun ρ : Fin m → ℕ => posS ρ s fb)).comp (meas_coord p).snd.fst
  refine Measurable.sub ?_ (Finset.measurable_sum _ fun k _ => (meas_coord k).fst)
  exact meas_index hpos (F := fun j (z : ℕ → Tr m) => (z p).2.2 j)
    fun j => (measurable_pi_apply j).comp (meas_coord p).snd.snd

lemma Aind_prod (β : ℝ) (p s : ℕ) (fb : Fin m) (z : ℕ → Tr m) :
    Aind p s z * ENNReal.ofReal (Real.exp (β * Xp p s fb z)) =
      ∏ k ∈ Finset.range (p + 1), (if k < p then fA β s (z k) else fB β s fb (z k)) := by
  rw [Finset.prod_range_succ, if_neg (lt_irrefl p),
    Finset.prod_congr rfl (fun k hk => if_pos (Finset.mem_range.1 hk))]
  unfold Aind fA fB
  by_cases hA : s ∈ Set.range (z p).2.1 ∧ ∀ k < p, s ∉ Set.range (z k).2.1
  · rw [if_pos hA, one_mul, if_pos hA.1, one_mul,
      Finset.prod_congr rfl (fun k hk => by rw [if_neg (hA.2 k (Finset.mem_range.1 hk)), one_mul])]
    unfold Xp
    have hexp : Real.exp (β * ((z p).2.2 (posS (z p).2.1 s fb) - ∑ k ∈ Finset.range (p + 1), (z k).1)) =
        (∏ k ∈ Finset.range (p + 1), Real.exp (-(β * (z k).1))) *
          Real.exp (β * (z p).2.2 (posS (z p).2.1 s fb)) := by
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      rw [mul_sub, Finset.mul_sum, Finset.sum_neg_distrib]
      ring
    rw [hexp, ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), Finset.prod_range_succ]
    ring
  · rw [if_neg hA, zero_mul]
    symm
    by_cases h1 : s ∈ Set.range (z p).2.1
    · push_neg at hA
      obtain ⟨k, hk, hk2⟩ := hA h1
      rw [Finset.prod_eq_zero (Finset.mem_range.2 hk) (by rw [if_pos hk2, zero_mul]), zero_mul]
    · rw [if_neg h1]; simp

lemma first_term (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam) {ζ : ℕ → Ω → Tr m}
    (h : IsIid P m n lam Bm ζ) (β : ℝ) (p s : ℕ) (fb : Fin m) :
    ∫⁻ ω, Aind p s (fun k => ζ k ω) * ENNReal.ofReal (Real.exp (β * Xp p s fb (fun k => ζ k ω))) ∂P =
      (∫⁻ t, fA β s t ∂(muT m n lam Bm)) ^ p * ∫⁻ t, fB β s fb t ∂(muT m n lam Bm) := by
  set g : ℕ → Tr m → ℝ≥0∞ := fun k => if k < p then fA β s else fB β s fb with hg
  have hgm : ∀ k, Measurable (g k) := by
    intro k; simp only [hg]; split_ifs
    · exact meas_fA β s
    · exact meas_fB β s fb
  have hpt : ∀ ω, Aind p s (fun k => ζ k ω) * ENNReal.ofReal (Real.exp (β * Xp p s fb (fun k => ζ k ω))) =
      ∏ k ∈ Finset.range (p + 1), g k (ζ k ω) := by
    intro ω
    rw [Aind_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hg]; split_ifs <;> rfl
  simp_rw [hpt]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ (fun k ω => g k (ζ k ω))
    (h.indep.comp g hgm) (fun k => (hgm k).comp (h.meas k))]
  have hint : ∀ k, ∫⁻ ω, g k (ζ k ω) ∂P = ∫⁻ t, g k t ∂(muT m n lam Bm) := by
    intro k
    rw [← h.law k, lintegral_map (hgm k) (h.meas k)]
  simp_rw [hint]
  rw [Finset.prod_range_succ, Finset.prod_congr rfl (fun k hk => by
    rw [show g k = fA β s from if_pos (Finset.mem_range.1 hk)]), Finset.prod_const,
    Finset.card_range]
  simp only [hg, lt_irrefl, if_false]

lemma cs_decomp (β : ℝ) (z : ℕ → Tr m) (ρ : Fin m → ℕ) (i : Fin m) (v : List (Fin m))
    (hap : ∃ k, ρ i ∈ Set.range (z k).2.1) :
    ENNReal.ofReal (Real.exp (β * cs z ρ (i :: v))) =
      ∑' p, Aind p (ρ i) z * ENNReal.ofReal (Real.exp (β * Xp p (ρ i) i z)) *
        ENNReal.ofReal (Real.exp (β * cs (shiftS (p + 1) z) (z p).2.1 v)) := by
  set T := srch z (ρ i) with hT
  have hTm : ρ i ∈ Set.range (z T).2.1 := Nat.sInf_mem hap
  have hA : ∀ p, Aind p (ρ i) z = if p = T then 1 else 0 := by
    intro p
    unfold Aind
    by_cases hp : p = T
    · rw [if_pos hp, if_pos]
      subst hp
      exact ⟨hTm, fun k hk h' => Nat.notMem_of_lt_sInf hk h'⟩
    · rw [if_neg hp, if_neg]
      rintro ⟨h1, h2⟩
      have hle : T ≤ p := Nat.sInf_le h1
      exact h2 T (lt_of_le_of_ne hle (Ne.symm hp)) hTm
  rw [tsum_eq_single T]
  · rw [hA, if_pos rfl, one_mul, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp only [cs]
    rw [← hT]
    unfold stepX Xp
    rw [← hT]
    ring
  · intro p hp
    rw [hA, if_neg hp, zero_mul, zero_mul]

lemma tail_bound {ζ : ℕ → Ω → Tr m} (h : IsIid P m n lam Bm ζ) (β : ℝ) (p : ℕ)
    (F : (ℕ → Tr m) → ℝ≥0∞) (hF : Measurable F) (g : (ℕ → Tr m) → (Fin m → ℕ)) (hg : Measurable g)
    (hloc : ∀ z z' : ℕ → Tr m, (∀ k ≤ p, z k = z' k) → F z = F z' ∧ g z = g z')
    (hgS : ∀ᵐ ω ∂P, ∀ i, g (fun k => ζ k ω) i < n) (v : List (Fin m)) (B : ℝ≥0∞)
    (IH : ∀ ζ' : ℕ → Ω → Tr m, IsIid P m n lam Bm ζ' → ∀ ρ : Fin m → ℕ, (∀ i, ρ i < n) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (β * cs (fun k => ζ' k ω) ρ v)) ∂P ≤ B) :
    ∫⁻ ω, F (fun k => ζ k ω) *
        ENNReal.ofReal (Real.exp (β * cs (fun k => ζ (p + 1 + k) ω) (g (fun k => ζ k ω)) v)) ∂P ≤
      B * ∫⁻ ω, F (fun k => ζ k ω) ∂P := by
  set Y : Ω → ℕ → Tr m := fun ω k => ζ (min k p) ω with hY
  set Z : Ω → ℕ → Tr m := fun ω k => ζ (p + 1 + k) ω with hZ
  have hYm : Measurable Y := measurable_pi_lambda _ fun k => h.meas _
  have hZm : Measurable Z := measurable_pi_lambda _ fun k => h.meas _
  have hYeq : ∀ ω, F (fun k => ζ k ω) = F (Y ω) ∧ g (fun k => ζ k ω) = g (Y ω) := by
    intro ω
    exact hloc _ _ fun k hk => by simp [hY, min_eq_left hk]
  set H : (ℕ → Tr m) × (ℕ → Tr m) → ℝ≥0∞ := fun q =>
    F q.1 * ENNReal.ofReal (Real.exp (β * cs q.2 (g q.1) v)) with hH
  have hHm : Measurable H := by
    refine (hF.comp measurable_fst).mul ?_
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((meas_cs_joint v).comp (measurable_snd.prodMk (hg.comp measurable_fst))).const_mul β))
  have hrw : ∀ ω, F (fun k => ζ k ω) *
      ENNReal.ofReal (Real.exp (β * cs (fun k => ζ (p + 1 + k) ω) (g (fun k => ζ k ω)) v)) =
      H (Y ω, Z ω) := by
    intro ω
    show _ = F (Y ω) * ENNReal.ofReal (Real.exp (β * cs (Z ω) (g (Y ω)) v))
    rw [← (hYeq ω).1, ← (hYeq ω).2]
  simp_rw [hrw]
  rw [indep_fubini hYm hZm (block_indep h.meas h.indep p) hHm]
  have hinner : ∀ y : ℕ → Tr m, ∫⁻ z, H (y, z) ∂(P.map Z) =
      F y * ∫⁻ ω, ENNReal.ofReal (Real.exp (β * cs (Z ω) (g y) v)) ∂P := by
    intro y
    have hm1 : Measurable (fun z : ℕ → Tr m => ENNReal.ofReal (Real.exp (β * cs z (g y) v))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((meas_cs v (g y)).const_mul β))
    have hm2 : Measurable (fun z : ℕ → Tr m => F y * ENNReal.ofReal (Real.exp (β * cs z (g y) v))) :=
      hm1.const_mul _
    show ∫⁻ z, F y * ENNReal.ofReal (Real.exp (β * cs z (g y) v)) ∂(P.map Z) = _
    rw [lintegral_map hm2 hZm]
    exact lintegral_const_mul _ (hm1.comp hZm)
  simp_rw [hinner]
  have hae : ∀ᵐ y ∂(P.map Y), F y * ∫⁻ ω, ENNReal.ofReal (Real.exp (β * cs (Z ω) (g y) v)) ∂P ≤
      F y * B := by
    have hset : MeasurableSet {y : ℕ → Tr m | ∀ i, g y i < n} :=
      hg (Set.to_countable {ρ : Fin m → ℕ | ∀ i, ρ i < n}).measurableSet
    have hgY : ∀ᵐ y ∂(P.map Y), ∀ i, g y i < n := by
      rw [ae_map_iff hYm.aemeasurable hset]
      filter_upwards [hgS] with ω hω
      rw [← (hYeq ω).2]
      exact hω
    filter_upwards [hgY] with y hy
    gcongr
    exact IH (fun k ω => ζ (p + 1 + k) ω) (h.tail p) _ hy
  calc _ ≤ ∫⁻ y, F y * B ∂(P.map Y) := lintegral_mono_ae hae
    _ = B * ∫⁻ ω, F (fun k => ζ k ω) ∂P := by
        rw [lintegral_mul_const _ hF, lintegral_map hF hYm, mul_comm]
        congr 1
        refine lintegral_congr fun ω => ?_
        exact (hYeq ω).1.symm


/-- the one-step factor `E[e^{βχ}] λm/(λm+β)` -/
noncomputable def rho1 (Bm : Measure (Fin m → ℝ)) (lam β : ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(pieceLaw Bm)) * ENNReal.ofReal (lam * m / (lam * m + β))

lemma claim (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam) {β : ℝ} (hβ : 0 < β) :
    ∀ (v : List (Fin m)) (ζ : ℕ → Ω → Tr m), IsIid P m n lam Bm ζ → ∀ ρ : Fin m → ℕ, (∀ i, ρ i < n) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (β * cs (fun k => ζ k ω) ρ v)) ∂P ≤ rho1 Bm lam β ^ v.length := by
  intro v
  induction v with
  | nil =>
    intro ζ _ ρ _
    simp [cs]
  | cons i v ih =>
    intro ζ h ρ hρ
    set s := ρ i with hs
    have hsn : s < n := hρ i
    have hdec : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (β * cs (fun k => ζ k ω) ρ (i :: v))) =
        ∑' p, Aind p s (fun k => ζ k ω) * ENNReal.ofReal (Real.exp (β * Xp p s i (fun k => ζ k ω))) *
          ENNReal.ofReal (Real.exp (β * cs (fun k => ζ (p + 1 + k) ω) (ζ p ω).2.1 v)) := by
      filter_upwards [h.ae_appears hm hn hlam hsn] with ω hω
      exact cs_decomp β (fun k => ζ k ω) ρ i v hω
    have hmeasF : ∀ p, Measurable (fun z : ℕ → Tr m =>
        Aind p s z * ENNReal.ofReal (Real.exp (β * Xp p s i z))) := fun p =>
      (meas_Aind p s).mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((meas_Xp p s i).const_mul β)))
    have hZ : Measurable (fun ω k => ζ k ω) := measurable_pi_lambda _ fun k => h.meas k
    rw [lintegral_congr_ae hdec, lintegral_tsum (fun p => by
      refine (((hmeasF p).comp hZ).mul ?_).aemeasurable
      refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.const_mul ?_ β))
      exact (meas_cs_joint v).comp ((measurable_pi_lambda _ fun k => h.meas (p + 1 + k)).prodMk
        (((meas_coord p).snd.fst).comp hZ)))]
    calc _ ≤ ∑' p, rho1 Bm lam β ^ v.length *
          ∫⁻ ω, Aind p s (fun k => ζ k ω) * ENNReal.ofReal (Real.exp (β * Xp p s i (fun k => ζ k ω))) ∂P := by
          refine ENNReal.tsum_le_tsum fun p => ?_
          refine tail_bound h β p _ (hmeasF p) (fun z => (z p).2.1) (meas_coord p).snd.fst ?_ ?_ v _ ih
          · intro z z' hzz
            refine ⟨?_, by rw [hzz p le_rfl]⟩
            unfold Aind Xp
            have e1 : ∀ k < p, z k = z' k := fun k hk => hzz k hk.le
            rw [hzz p le_rfl, Finset.sum_congr rfl (fun k hk => by
              rw [hzz k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))])]
            congr 2
            apply propext
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨h1, fun k hk => by rw [← e1 k hk]; exact h2 k hk⟩
            · rintro ⟨h1, h2⟩; exact ⟨h1, fun k hk => by rw [e1 k hk]; exact h2 k hk⟩
          · filter_upwards [h.ae_inj hm hn hlam] with ω hω
            exact (hω p).2
      _ = rho1 Bm lam β ^ v.length * ∑' p, (∫⁻ t, fA β s t ∂(muT m n lam Bm)) ^ p *
            ∫⁻ t, fB β s i t ∂(muT m n lam Bm) := by
          rw [ENNReal.tsum_mul_left]
          congr 1
          exact tsum_congr fun p => first_term hm hn hlam h β p s i
      _ ≤ rho1 Bm lam β ^ v.length * rho1 Bm lam β := by
          gcongr
          exact geom_bound hm hn hlam hβ hsn i
      _ = rho1 Bm lam β ^ (i :: v).length := by
          rw [List.length_cons, pow_succ]

end Core

end SQE63

open SQE63 in
theorem solution {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {n : ℕ} (hn : m ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ) (R : ℕ → Ω → (Fin m → ℕ)) (C : ℕ → Ω → (Fin m → ℝ))
    (hsys : IsSyncSystem P m n lam Bm E R C)
    {β : ℝ} (hβ : 0 < β) (r : ℕ) :
    P {ω | 0 < Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r} ≤
        ∫⁻ ω, ∑ v : Fin r → Fin m,
          ENNReal.ofReal (Real.exp (β * pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) (List.ofFn v))) ∂P ∧
      ∫⁻ ω, ∑ v : Fin r → Fin m,
          ENNReal.ofReal (Real.exp (β * pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) (List.ofFn v))) ∂P ≤
        rho Bm lam β ^ r := by
  have hE : ∀ k, Measurable (E k) := fun k => (hsys.1 k).1
  have hR : ∀ k, Measurable (R k) := fun k => (hsys.1 k).2.1
  have hC : ∀ k, Measurable (C k) := fun k => (hsys.1 k).2.2
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hmeasv : ∀ v : Fin r → Fin m, Measurable (fun ω => ENNReal.ofReal (Real.exp (β *
      pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) (List.ofFn v)))) := fun v =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((meas_pathSumHat hE hR hC _).const_mul β))
  constructor
  · -- Markov
    have h1 : {ω | 0 < Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r} ⊆
        {ω | 1 ≤ ∑ v : Fin r → Fin m, ENNReal.ofReal (Real.exp (β * pathSumHat (fun k => E k ω)
          (fun k => R k ω) (fun k => C k ω) (List.ofFn v)))} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      obtain ⟨v, hv⟩ := exists_eq_ciSup_of_finite (f := fun v : Fin r → Fin m =>
        pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) (List.ofFn v))
      unfold Uhat at hω
      rw [← hv] at hω
      refine le_trans ?_ (Finset.single_le_sum (f := fun v : Fin r → Fin m =>
        ENNReal.ofReal (Real.exp (β * pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω)
          (List.ofFn v)))) (fun _ _ => zero_le) (Finset.mem_univ v))
      rw [ENNReal.one_le_ofReal]
      exact Real.one_le_exp (by positivity)
    calc _ ≤ _ := measure_mono h1
      _ = 1 * P {ω | 1 ≤ ∑ v : Fin r → Fin m, ENNReal.ofReal (Real.exp (β * pathSumHat (fun k => E k ω)
          (fun k => R k ω) (fun k => C k ω) (List.ofFn v)))} := (one_mul _).symm
      _ ≤ _ := mul_meas_ge_le_lintegral₀ (Finset.measurable_sum _ fun v _ => hmeasv v).aemeasurable 1
  · -- comparison with the tree, path by path
    set ξ : ℕ → Ω → Tr m := fun k ω => (E k ω, R k ω, C k ω) with hξ
    have hiid : IsIid P m n lam Bm ξ := ⟨fun k => (hE k).prodMk ((hR k).prodMk (hC k)), hsys.2.1,
      fun k => hsys.2.2 k⟩
    have hgood := ae_good hm hn hlam hsys
    have hword : ∀ v : List (Fin m), ∫⁻ ω, ENNReal.ofReal (Real.exp (β * pathSumHat (fun k => E k ω)
        (fun k => R k ω) (fun k => C k ω) v)) ∂P ≤ rho1 Bm lam β ^ v.length := by
      intro v
      calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (β * cs (fun k => ξ (0 + 1 + k) ω) (R 0 ω) v)) ∂P := by
            refine lintegral_mono_ae ?_
            filter_upwards [hgood] with ω hω
            obtain ⟨hE0, -, hS, hsrv⟩ := hω
            have hpred : ∀ k i, ∃ k', k < k' ∧ R k ω i ∈ Set.range (R k' ω) := by
              intro k i
              obtain ⟨k', h1, h2⟩ := ((hsrv _ ((hS k).2 i)).and_eventually (eventually_gt_atTop k)).exists
              exact ⟨k', h2, h1⟩
            have := pathSumHat_le_cs (C := fun k => C k ω) (E := fun k => E k ω) hpred (hE0 0).le v
            apply ENNReal.ofReal_le_ofReal
            apply Real.exp_le_exp.2
            apply mul_le_mul_of_nonneg_left _ hβ.le
            exact this
        _ = ∫⁻ ω, (fun _ => (1 : ℝ≥0∞)) (fun k => ξ k ω) *
              ENNReal.ofReal (Real.exp (β * cs (fun k => ξ (0 + 1 + k) ω)
                ((fun z : ℕ → Tr m => (z 0).2.1) (fun k => ξ k ω)) v)) ∂P := by
            simp [hξ]
        _ ≤ rho1 Bm lam β ^ v.length * ∫⁻ ω, (fun _ => (1 : ℝ≥0∞)) (fun k => ξ k ω) ∂P :=
            tail_bound hiid β 0 (fun _ => 1) measurable_const (fun z => (z 0).2.1)
              (meas_coord 0).snd.fst (fun z z' hzz => ⟨rfl, by rw [hzz 0 le_rfl]⟩)
              (by filter_upwards [hiid.ae_inj hm hn hlam] with ω hω; exact (hω 0).2) v _
              (claim hm hn hlam hβ v)
        _ = rho1 Bm lam β ^ v.length := by simp
    rw [lintegral_finset_sum _ fun v _ => hmeasv v]
    calc _ ≤ ∑ v : Fin r → Fin m, rho1 Bm lam β ^ r := by
          refine Finset.sum_le_sum fun v _ => ?_
          have := hword (List.ofFn v)
          rwa [List.length_ofFn] at this
      _ = rho Bm lam β ^ r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_pow, ← mul_pow]
          unfold rho rho1
          rw [mul_assoc]
