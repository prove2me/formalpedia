-- Prove2me | solution 1 for PartialResampling.pra_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:47:46.058851+00:00
-- url     : https://prove2.me/submissions/bc8e1099-f145-469e-910f-53228e1803ed

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_newPath_not_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_newPath_deeper_than_candidate
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPaths_pathsToTree
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessWeight_eq_prod_paths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_succ
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyWitness_ne_of_root_count_ne

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open Finset

namespace PRAcore

variable {I : Type} [Fintype I] [DecidableEq I] {Ω : I → Type} [∀ i, Fintype (Ω i)]
  [∀ i, DecidableEq (Ω i)] {T : Type} [Fintype T] [DecidableEq T]

/-- labels: (atomic set, event) -/
abbrev Lab (Ω : I → Type) (T : Type) := (∀ i, Option (Ω i)) × T

def supp (Y : ∀ i, Option (Ω i)) : Finset I := univ.filter (fun i => (Y i).isSome)

def lvars (ℓ : Lab Ω T) : Finset (I ⊕ T) := (supp ℓ.1).map Function.Embedding.inl ∪ {Sum.inr ℓ.2}

abbrev G (Ω : I → Type) [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)] (T : Type) [Fintype T]
    [DecidableEq T] : SimpleGraph (Lab Ω T) := supportGraph (lvars (Ω := Ω) (T := T))

theorem mem_lvars_inl (ℓ : Lab Ω T) (i : I) : Sum.inl i ∈ lvars ℓ ↔ (ℓ.1 i).isSome := by
  simp [lvars, supp]

theorem mem_lvars_inr (ℓ : Lab Ω T) (k : T) : Sum.inr k ∈ lvars ℓ ↔ k = ℓ.2 := by
  simp [lvars, supp]

theorem related_iff (ℓ ℓ' : Lab Ω T) :
    ℓ' ∈ closedNeighbors (G Ω T) ℓ ↔ (ℓ'.2 = ℓ.2 ∨ ∃ i, (ℓ.1 i).isSome ∧ (ℓ'.1 i).isSome) := by
  rw [mem_closedNeighbors]
  constructor
  · rintro (rfl | ⟨_, h⟩)
    · exact Or.inl rfl
    · rw [Finset.not_disjoint_iff] at h
      obtain ⟨a, ha, hb⟩ := h
      rcases a with i | k
      · exact Or.inr ⟨i, (mem_lvars_inl _ _).1 ha, (mem_lvars_inl _ _).1 hb⟩
      · left; rw [mem_lvars_inr] at ha hb; rw [← hb, ha]
  · intro h
    by_cases he : ℓ' = ℓ
    · exact Or.inl he
    · right
      refine ⟨fun h' => he h'.symm, ?_⟩
      rw [Finset.not_disjoint_iff]
      rcases h with h | ⟨i, hi, hi'⟩
      · exact ⟨Sum.inr ℓ.2, (mem_lvars_inr _ _).2 rfl, (mem_lvars_inr _ _).2 h.symm⟩
      · exact ⟨Sum.inl i, (mem_lvars_inl _ _).2 hi, (mem_lvars_inl _ _).2 hi'⟩

/-- indicator that the atomic set holds on z -/
def hold (Y : ∀ i, Option (Ω i)) (z : ∀ i, Ω i) : ℝ :=
  ∏ i, (Y i).elim 1 (fun ω => if z i = ω then 1 else 0)

def Holds (Y : ∀ i, Option (Ω i)) (z : ∀ i, Ω i) : Prop := ∀ i ω, Y i = some ω → z i = ω

theorem hold_eq_one (Y : ∀ i, Option (Ω i)) (z : ∀ i, Ω i) (h : Holds Y z) : hold Y z = 1 := by
  unfold hold
  refine Finset.prod_eq_one (fun i _ => ?_)
  cases hY : Y i with
  | none => rfl
  | some ω => simp [h i ω hY]

theorem hold_eq_zero (Y : ∀ i, Option (Ω i)) (z : ∀ i, Ω i) (h : ¬ Holds Y z) : hold Y z = 0 := by
  unfold Holds at h
  push_neg at h
  obtain ⟨i, ω, hY, hz⟩ := h
  unfold hold
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [hY, hz]

theorem hold_nonneg (Y : ∀ i, Option (Ω i)) (z : ∀ i, Ω i) : 0 ≤ hold Y z := by
  by_cases h : Holds Y z
  · rw [hold_eq_one Y z h]; norm_num
  · rw [hold_eq_zero Y z h]

/-- resampling kernel -/
def res (p : ∀ i, Ω i → ℝ) (Y : ∀ i, Option (Ω i)) (z z' : ∀ i, Ω i) : ℝ :=
  ∏ i, (Y i).elim (if z' i = z i then 1 else 0) (fun _ => p i (z' i))

theorem res_nonneg (p : ∀ i, Ω i → ℝ) (hp : ∀ i ω, 0 < p i ω) (Y : ∀ i, Option (Ω i))
    (z z' : ∀ i, Ω i) : 0 ≤ res p Y z z' := by
  unfold res
  refine Finset.prod_nonneg (fun i _ => ?_)
  cases Y i with
  | none => simp only [Option.elim]; split_ifs <;> norm_num
  | some _ => exact (hp _ _).le

/-- sum of a product-form function against the resampling kernel -/
theorem sum_res_prod (p : ∀ i, Ω i → ℝ) (Y : ∀ i, Option (Ω i)) (z : ∀ i, Ω i)
    (f : ∀ i, Ω i → ℝ) :
    ∑ z' : (∀ i, Ω i), res p Y z z' * ∏ i, f i (z' i) =
      ∏ i, (Y i).elim (f i (z i)) (fun _ => ∑ ω, p i ω * f i ω) := by
  unfold res
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i ω => (Y i).elim (if ω = z i then 1 else 0) (fun _ => p i ω) * f i ω)]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases Y i with
  | none => simp [Option.elim]
  | some _ => rfl

theorem sum_res (p : ∀ i, Ω i → ℝ) (hp1 : ∀ i, ∑ ω, p i ω = 1) (Y : ∀ i, Option (Ω i))
    (z : ∀ i, Ω i) : ∑ z' : (∀ i, Ω i), res p Y z z' = 1 := by
  have := sum_res_prod p Y z (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at this
  rw [this]
  refine Finset.prod_eq_one (fun i _ => ?_)
  cases Y i with
  | none => rfl
  | some _ => simpa using hp1 i


section Process
variable (p : ∀ i, Ω i → ℝ) (q : T → (∀ i, Option (Ω i)) → ℝ) (κ : (∀ i, Ω i) → T)

noncomputable def qs (z : ∀ i, Ω i) : ℝ := ∑ Y, q (κ z) Y * hold Y z
noncomputable def sel (z : ∀ i, Ω i) (Y : ∀ i, Option (Ω i)) : ℝ := q (κ z) Y * hold Y z / qs q κ z

noncomputable def Ex : ℕ → (∀ i, Ω i) → (List (Lab Ω T) → ℝ) → ℝ
  | 0, _, F => F []
  | n + 1, z, F => ∑ Y, sel q κ z Y * ∑ z', res p Y z z' * Ex n z' (fun r => F ((Y, κ z) :: r))

variable {p q κ}

theorem sel_nonneg (hq : ∀ k Y, 0 ≤ q k Y) (hqs : ∀ z, 1 ≤ qs q κ z) (z : ∀ i, Ω i) (Y) :
    0 ≤ sel q κ z Y :=
  div_nonneg (mul_nonneg (hq _ _) (hold_nonneg _ _)) (by linarith [hqs z])

theorem sel_le (hq : ∀ k Y, 0 ≤ q k Y) (hqs : ∀ z, 1 ≤ qs q κ z) (z : ∀ i, Ω i) (Y) :
    sel q κ z Y ≤ q (κ z) Y * hold Y z := by
  unfold sel
  rw [div_le_iff₀ (by linarith [hqs z])]
  have := mul_nonneg (hq (κ z) Y) (hold_nonneg Y z)
  nlinarith [hqs z]

theorem sum_sel (hqs : ∀ z, 1 ≤ qs q κ z) (z : ∀ i, Ω i) : ∑ Y, sel q κ z Y = 1 := by
  unfold sel
  rw [← Finset.sum_div]
  have h1 := hqs z
  unfold qs at h1
  exact div_self (by linarith)

theorem sel_eq_zero (z : ∀ i, Ω i) (Y) (h : ¬ Holds Y z) : sel q κ z Y = 0 := by
  unfold sel; rw [hold_eq_zero Y z h]; simp

theorem Ex_mono (hp : ∀ i ω, 0 < p i ω) (hq : ∀ k Y, 0 ≤ q k Y) (hqs : ∀ z, 1 ≤ qs q κ z) :
    ∀ (n : ℕ) (z : ∀ i, Ω i) (F F' : List (Lab Ω T) → ℝ),
      (∀ r : List (Lab Ω T), r.length ≤ n → F r ≤ F' r) → Ex p q κ n z F ≤ Ex p q κ n z F'
  | 0, z, F, F', h => h [] (by simp)
  | n + 1, z, F, F', h => by
    simp only [Ex]
    refine Finset.sum_le_sum (fun Y _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun z' _ => mul_le_mul_of_nonneg_left ?_ (res_nonneg p hp _ _ _)))
      (sel_nonneg hq hqs _ _))
    exact Ex_mono hp hq hqs n z' _ _ (fun r hr => h _ (by simp; omega))

theorem Ex_affine (hp1 : ∀ i, ∑ ω, p i ω = 1) (hqs : ∀ z, 1 ≤ qs q κ z) :
    ∀ (n : ℕ) (z : ∀ i, Ω i) (a b : ℝ) (F : List (Lab Ω T) → ℝ),
      Ex p q κ n z (fun r => a + b * F r) = a + b * Ex p q κ n z F
  | 0, z, a, b, F => rfl
  | n + 1, z, a, b, F => by
    simp only [Ex]
    have key : ∀ z' Y, Ex p q κ n z' (fun r => a + b * F ((Y, κ z) :: r)) =
        a + b * Ex p q κ n z' (fun r => F ((Y, κ z) :: r)) :=
      fun z' Y => Ex_affine hp1 hqs n z' a b (fun r => F ((Y, κ z) :: r))
    simp_rw [key]
    have h1 : ∀ Y, ∑ z', res p Y z z' * (a + b * Ex p q κ n z' (fun r => F ((Y, κ z) :: r))) =
        a + b * ∑ z', res p Y z z' * Ex p q κ n z' (fun r => F ((Y, κ z) :: r)) := by
      intro Y
      have e : ∑ z', res p Y z z' * (a + b * Ex p q κ n z' (fun r => F ((Y, κ z) :: r))) =
          a * ∑ z', res p Y z z' + b * ∑ z', res p Y z z' * Ex p q κ n z' (fun r => F ((Y, κ z) :: r)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun z' _ => by ring)
      rw [e, sum_res p hp1, mul_one]
    simp_rw [h1]
    have e2 : ∑ Y, sel q κ z Y * (a + b * ∑ z', res p Y z z' * Ex p q κ n z' (fun r => F ((Y, κ z) :: r))) =
        a * ∑ Y, sel q κ z Y + b * ∑ Y, sel q κ z Y * ∑ z', res p Y z z' * Ex p q κ n z' (fun r => F ((Y, κ z) :: r)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun Y _ => by ring)
    rw [e2, sum_sel hqs, mul_one]

theorem Ex_add : ∀ (n : ℕ) (z : ∀ i, Ω i) (F F' : List (Lab Ω T) → ℝ),
      Ex p q κ n z (fun r => F r + F' r) = Ex p q κ n z F + Ex p q κ n z F'
  | 0, z, F, F' => rfl
  | n + 1, z, F, F' => by
    simp only [Ex]
    have key : ∀ z' Y, Ex p q κ n z' (fun r => F ((Y, κ z) :: r) + F' ((Y, κ z) :: r)) =
        Ex p q κ n z' (fun r => F ((Y, κ z) :: r)) + Ex p q κ n z' (fun r => F' ((Y, κ z) :: r)) :=
      fun z' Y => Ex_add n z' (fun r => F ((Y, κ z) :: r)) (fun r => F' ((Y, κ z) :: r))
    simp_rw [key, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Y _ => by ring)

theorem Ex_zero : ∀ (n : ℕ) (z : ∀ i, Ω i), Ex p q κ n z (fun _ => 0) = 0
  | 0, z => rfl
  | n + 1, z => by
    simp only [Ex]
    simp_rw [Ex_zero n, mul_zero, Finset.sum_const_zero, mul_zero, Finset.sum_const_zero]

theorem Ex_sum {α : Type} (s : Finset α) (n : ℕ) (z : ∀ i, Ω i) (F : α → List (Lab Ω T) → ℝ) :
    Ex p q κ n z (fun r => ∑ a ∈ s, F a r) = ∑ a ∈ s, Ex p q κ n z (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Ex_zero n z
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [Ex_add n z (F a) (fun r => ∑ a ∈ s, F a r), ih]

theorem Ex_length (hp1 : ∀ i, ∑ ω, p i ω = 1) (hqs : ∀ z, 1 ≤ qs q κ z) :
    ∀ (n : ℕ) (z : ∀ i, Ω i), Ex p q κ n z (fun r => (r.length : ℝ)) = n
  | 0, z => by simp [Ex]
  | n + 1, z => by
    simp only [Ex, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h : ∀ z', Ex p q κ n z' (fun r => (r.length : ℝ) + 1) = n + 1 := by
      intro z'
      have := Ex_affine hp1 hqs n z' 1 1 (fun r => (r.length : ℝ))
      simp only [one_mul] at this
      rw [show (fun r : List (Lab Ω T) => (r.length : ℝ) + 1) = (fun r => 1 + (r.length : ℝ)) from
        funext (fun r => add_comm _ _), this, Ex_length hp1 hqs n z']
      ring
    simp_rw [h, ← Finset.sum_mul, sum_res p hp1, one_mul, ← Finset.sum_mul, sum_sel hqs, one_mul]

end Process

section Appear

/-- the tree with root `ρ` and path set `P` appears in the run -/
def appears (ρ : Lab Ω T) (P : Finset (List (Lab Ω T))) : List (Lab Ω T) → Prop
  | [] => False
  | U :: run => (U = ρ ∧ P = {[]}) ∨
      ∃ P', extendWitness (G Ω T) ρ U P' = P ∧ appears ρ P' run

theorem appears_nil_mem (ρ : Lab Ω T) : ∀ (run : List (Lab Ω T)) (P : Finset (List (Lab Ω T))),
    appears ρ P run → [] ∈ P
  | [], P, h => h.elim
  | U :: run, P, h => by
    rcases h with ⟨_, rfl⟩ | ⟨P', rfl, h'⟩
    · simp
    · exact subset_extendWitness _ ρ U P' (appears_nil_mem ρ run P' h')

theorem appears_history : ∀ (run : List (Lab Ω T)) (t : ℕ) (ht : t < run.length),
    appears run[t] (historyWitness (G Ω T) run[t] (run.take t)) run
  | [], t, ht => by simp at ht
  | U :: run, 0, ht => by
    simp only [appears]
    left; simp [historyWitness]
  | U :: run, t + 1, ht => by
    simp only [appears, List.getElem_cons_succ, List.take_succ_cons]
    right
    exact ⟨_, rfl, appears_history run t (by simpa using ht)⟩

end Appear


section Tree
variable (p : ∀ i, Ω i → ℝ) (q : T → (∀ i, Option (Ω i)) → ℝ)

noncomputable def ind (P : Prop) : ℝ := @ite ℝ P (Classical.propDecidable P) 1 0

theorem ind_pos {P : Prop} (h : P) : ind P = 1 := by
  unfold ind; exact @if_pos _ (Classical.propDecidable P) h _ _ _
theorem ind_neg {P : Prop} (h : ¬ P) : ind P = 0 := by
  unfold ind; exact @if_neg _ (Classical.propDecidable P) h _ _ _
theorem ind_nonneg (P : Prop) : 0 ≤ ind P := by
  by_cases h : P
  · rw [ind_pos h]; norm_num
  · rw [ind_neg h]
theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  by_cases h : P
  · rw [ind_pos h]
  · rw [ind_neg h]; norm_num
theorem ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  by_cases hP : P
  · rw [ind_pos hP, ind_pos (h hP)]
  · rw [ind_neg hP]; exact ind_nonneg Q

noncomputable def pw (ℓ : Lab Ω T) : ℝ := (∏ i, (ℓ.1 i).elim 1 (p i)) * q ℓ.2 ℓ.1

def inodes (ρ : Lab Ω T) (P : Finset (List (Lab Ω T))) (i : I) : Finset (List (Lab Ω T)) :=
  P.filter (fun r => ((pathLabel ρ r).1 i).isSome)

noncomputable def deep (S : Finset (List (Lab Ω T))) (h : S.Nonempty) : List (Lab Ω T) :=
  Classical.choose (S.exists_max_image List.length h)

theorem deep_spec (S : Finset (List (Lab Ω T))) (h : S.Nonempty) :
    deep S h ∈ S ∧ ∀ r ∈ S, r.length ≤ (deep S h).length :=
  Classical.choose_spec (S.exists_max_image List.length h)

noncomputable def facV (ρ : Lab Ω T) (i : I) (S : Finset (List (Lab Ω T))) (x : Ω i) : ℝ :=
  if h : S.Nonempty then
    ((pathLabel ρ (deep S h)).1 i).elim 1 (fun ω => (if x = ω then 1 else 0) / p i ω)
  else 1

noncomputable def wt (ρ : Lab Ω T) (P : Finset (List (Lab Ω T))) : ℝ :=
  ∏ r ∈ P, pw p q (pathLabel ρ r)

noncomputable def Bound (z : ∀ i, Ω i) (ρ : Lab Ω T) (P : Finset (List (Lab Ω T))) : ℝ :=
  wt p q ρ P * ∏ i, facV p ρ i (inodes ρ P i) (z i)

variable {p q}

theorem facV_nonneg (hp : ∀ i ω, 0 < p i ω) (ρ : Lab Ω T) (i : I) (S) (x : Ω i) :
    0 ≤ facV p ρ i S x := by
  unfold facV
  split_ifs with h
  · cases ((pathLabel ρ (deep S h)).1 i) with
    | none => norm_num
    | some ω => exact div_nonneg (by split_ifs <;> norm_num) (hp i ω).le
  · norm_num

theorem facV_empty (ρ : Lab Ω T) (i : I) (x : Ω i) : facV p ρ i ∅ x = 1 := by
  unfold facV; simp

theorem sum_facV (hp : ∀ i ω, 0 < p i ω) (hp1 : ∀ i, ∑ ω, p i ω = 1) (ρ : Lab Ω T) (i : I) (S) :
    ∑ x, p i x * facV p ρ i S x = 1 := by
  unfold facV
  split_ifs with h
  · cases ((pathLabel ρ (deep S h)).1 i) with
    | none => simpa using hp1 i
    | some ω =>
      simp only [Option.elim]
      rw [Finset.sum_eq_single ω]
      · simp only [if_true]; field_simp [(hp i ω).ne']
      · intro b _ hb; simp [hb]
      · simp
  · simpa using hp1 i

theorem pw_nonneg (hp : ∀ i ω, 0 < p i ω) (hq : ∀ k Y, 0 ≤ q k Y) (ℓ : Lab Ω T) : 0 ≤ pw p q ℓ := by
  unfold pw
  refine mul_nonneg (Finset.prod_nonneg (fun i _ => ?_)) (hq _ _)
  cases ℓ.1 i with
  | none => norm_num
  | some ω => exact (hp i ω).le

theorem Bound_nonneg (hp : ∀ i ω, 0 < p i ω) (hq : ∀ k Y, 0 ≤ q k Y) (z : ∀ i, Ω i)
    (ρ : Lab Ω T) (P : Finset (List (Lab Ω T))) : 0 ≤ Bound p q z ρ P :=
  mul_nonneg (Finset.prod_nonneg (fun r _ => pw_nonneg hp hq _))
    (Finset.prod_nonneg (fun i _ => facV_nonneg hp _ _ _ _))

/-- facts about a genuine extension step -/
def ExtFacts (ρ U : Lab Ω T) (P' P : Finset (List (Lab Ω T))) (w : List (Lab Ω T)) : Prop :=
  w ∉ P' ∧ P = insert w P' ∧ pathLabel ρ w = U ∧
    ∀ r ∈ P', U ∈ closedNeighbors (G Ω T) (pathLabel ρ r) → r.length < w.length

theorem ext_cases (ρ U : Lab Ω T) (P' P : Finset (List (Lab Ω T)))
    (h : extendWitness (G Ω T) ρ U P' = P) :
    (P' = P ∧ ∀ r ∈ P, U ∉ closedNeighbors (G Ω T) (pathLabel ρ r)) ∨ ∃ w, ExtFacts ρ U P' P w := by
  unfold extendWitness at h
  split_ifs at h with hc
  · right
    refine ⟨attachmentParent (G Ω T) ρ U P' hc ++ [U], newPath_not_mem _ ρ U P' hc, h.symm,
      pathLabel_append_singleton _ _ _, ?_⟩
    intro r hr hU
    exact newPath_deeper_than_candidate _ ρ U P' hc r (Finset.mem_filter.mpr ⟨hr, hU⟩)
  · left
    refine ⟨h, ?_⟩
    intro r hr hU
    subst h
    exact hc ⟨r, Finset.mem_filter.mpr ⟨hr, hU⟩⟩

theorem sum_res_Bound (hp : ∀ i ω, 0 < p i ω) (hp1 : ∀ i, ∑ ω, p i ω = 1)
    (Y : ∀ i, Option (Ω i)) (z : ∀ i, Ω i) (ρ : Lab Ω T) (P : Finset (List (Lab Ω T))) :
    ∑ z', res p Y z z' * Bound p q z' ρ P =
      wt p q ρ P * ∏ i, (Y i).elim (facV p ρ i (inodes ρ P i) (z i)) (fun _ => 1) := by
  unfold Bound
  have e : ∀ z' : (∀ i, Ω i), res p Y z z' * (wt p q ρ P * ∏ i, facV p ρ i (inodes ρ P i) (z' i)) =
      wt p q ρ P * (res p Y z z' * ∏ i, facV p ρ i (inodes ρ P i) (z' i)) := fun z' => by ring
  simp_rw [e]
  rw [← Finset.mul_sum, sum_res_prod p Y z (fun i x => facV p ρ i (inodes ρ P i) x)]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases Y i with
  | none => rfl
  | some _ => exact sum_facV hp hp1 ρ i _

theorem Bound_ext (hp : ∀ i ω, 0 < p i ω) (ρ : Lab Ω T) (Y : ∀ i, Option (Ω i)) (k : T)
    (P' P : Finset (List (Lab Ω T))) (w : List (Lab Ω T)) (hF : ExtFacts ρ (Y, k) P' P w)
    (z : ∀ i, Ω i) (hY : Holds Y z) :
    Bound p q z ρ P = q k Y * (wt p q ρ P' *
      ∏ i, (Y i).elim (facV p ρ i (inodes ρ P' i) (z i)) (fun _ => 1)) := by
  obtain ⟨hw, hP, hl, hdeep⟩ := hF
  subst hP
  unfold Bound wt
  rw [Finset.prod_insert hw, hl]
  have hfac : ∀ i, facV p ρ i (inodes ρ (insert w P') i) (z i) =
      (Y i).elim (facV p ρ i (inodes ρ P' i) (z i)) (fun ω => 1 / p i ω) := by
    intro i
    unfold inodes
    rw [Finset.filter_insert, hl]
    cases hYi : Y i with
    | none => simp [hYi]
    | some ω =>
      simp only [hYi, Option.isSome_some, if_true, Option.elim]
      set S := insert w (Finset.filter (fun r => ((pathLabel ρ r).1 i).isSome) P') with hS
      have hne : S.Nonempty := ⟨w, Finset.mem_insert_self _ _⟩
      have hd : deep S hne = w := by
        obtain ⟨hdm, hmax⟩ := deep_spec S hne
        by_contra hne'
        rcases Finset.mem_insert.mp hdm with h1 | h1
        · exact hne' h1
        · obtain ⟨hdP, hdi⟩ := Finset.mem_filter.mp h1
          have hrel : (Y, k) ∈ closedNeighbors (G Ω T) (pathLabel ρ (deep S hne)) := by
            rw [related_iff]
            exact Or.inr ⟨i, hdi, by simp [hYi]⟩
          have h2 := hdeep _ hdP hrel
          have h3 := hmax w (Finset.mem_insert_self _ _)
          omega
      unfold facV
      rw [dif_pos hne]
      simp only [hd, hl, hYi, Option.elim, hY i ω hYi, if_true]
  simp_rw [hfac]
  generalize (∏ r ∈ P', pw p q (pathLabel ρ r)) = W
  have hAB : (∏ i, (Y i).elim 1 (p i)) * (∏ i, (Y i).elim (facV p ρ i (inodes ρ P' i) (z i))
      (fun ω => 1 / p i ω)) = ∏ i, (Y i).elim (facV p ρ i (inodes ρ P' i) (z i)) (fun _ => 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    cases Y i with
    | none => simp
    | some ω => simp only [Option.elim]; field_simp [(hp i ω).ne']
  unfold pw
  simp only
  rw [← hAB]
  ring

end Tree


section Main
variable {p : ∀ i, Ω i → ℝ} {q : T → (∀ i, Option (Ω i)) → ℝ} {κ : (∀ i, Ω i) → T}

theorem Ex_const (hp1 : ∀ i, ∑ ω, p i ω = 1) (hqs : ∀ z, 1 ≤ qs q κ z) (n : ℕ) (z : ∀ i, Ω i)
    (c : ℝ) : Ex p q κ n z (fun _ => c) = c := by
  have := Ex_affine hp1 hqs n z c 0 (fun _ => 0)
  simpa using this

theorem sum_res_Bound_free (hp : ∀ i ω, 0 < p i ω) (hp1 : ∀ i, ∑ ω, p i ω = 1)
    (Y : ∀ i, Option (Ω i)) (k : T) (z : ∀ i, Ω i) (ρ : Lab Ω T) (P : Finset (List (Lab Ω T)))
    (hfree : ∀ r ∈ P, (Y, k) ∉ closedNeighbors (G Ω T) (pathLabel ρ r)) :
    ∑ z', res p Y z z' * Bound p q z' ρ P = Bound p q z ρ P := by
  rw [sum_res_Bound hp hp1]
  unfold Bound
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases hYi : Y i with
  | none => rfl
  | some ω =>
    have : inodes ρ P i = ∅ := by
      unfold inodes
      rw [Finset.filter_eq_empty_iff]
      intro r hr hri
      exact hfree r hr ((related_iff _ _).2 (Or.inr ⟨i, hri, by simp [hYi]⟩))
    simp [this, facV_empty]

noncomputable def Jset (κ : (∀ i, Ω i) → T) (z : ∀ i, Ω i) (ρ : Lab Ω T) (P : Finset (List (Lab Ω T))) :
    Finset (List (Lab Ω T)) :=
  @Finset.filter _ (fun r => (pathLabel ρ r).2 = κ z ∧ Holds (pathLabel ρ r).1 z)
    (fun _ => Classical.propDecidable _) P

theorem mem_Jset (z : ∀ i, Ω i) (ρ : Lab Ω T) (P : Finset (List (Lab Ω T))) (r : List (Lab Ω T)) :
    r ∈ Jset κ z ρ P ↔ r ∈ P ∧ (pathLabel ρ r).2 = κ z ∧ Holds (pathLabel ρ r).1 z := by
  unfold Jset; exact @Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _

theorem appear_bound (hp : ∀ i ω, 0 < p i ω) (hp1 : ∀ i, ∑ ω, p i ω = 1)
    (hq : ∀ k Y, 0 ≤ q k Y) (hqs : ∀ z, 1 ≤ qs q κ z) (ρ : Lab Ω T) :
    ∀ (n : ℕ) (z : ∀ i, Ω i) (P : Finset (List (Lab Ω T))),
      Ex p q κ n z (fun r => ind (appears ρ P r)) ≤ Bound p q z ρ P
  | 0, z, P => by
    simp only [Ex]
    rw [ind_neg (show ¬ appears ρ P [] from fun h => h)]
    exact Bound_nonneg hp hq z ρ P
  | n + 1, z, P => by
    simp only [Ex]
    have IH := appear_bound hp hp1 hq hqs ρ n
    -- general term bound
    have term_le : ∀ Y (B : ℝ), 0 ≤ B → (∀ z', Ex p q κ n z' (fun r => ind (appears ρ P ((Y, κ z) :: r))) ≤
        B * Bound p q z' ρ P) → sel q κ z Y * ∑ z', res p Y z z' *
          Ex p q κ n z' (fun r => ind (appears ρ P ((Y, κ z) :: r))) ≤
        sel q κ z Y * (B * ∑ z', res p Y z z' * Bound p q z' ρ P) := by
      intro Y B hB h
      refine mul_le_mul_of_nonneg_left ?_ (sel_nonneg hq hqs z Y)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun z' _ => ?_)
      have := mul_le_mul_of_nonneg_left (h z') (res_nonneg p hp Y z z')
      linarith
    have zero_of : ∀ Y, (∀ r, ¬ appears ρ P ((Y, κ z) :: r)) →
        sel q κ z Y * ∑ z', res p Y z z' *
          Ex p q κ n z' (fun r => ind (appears ρ P ((Y, κ z) :: r))) = 0 := by
      intro Y h
      have : ∀ z', Ex p q κ n z' (fun r => ind (appears ρ P ((Y, κ z) :: r))) = 0 := by
        intro z'
        have e : (fun r => ind (appears ρ P ((Y, κ z) :: r))) = fun _ => (0 : ℝ) :=
          funext (fun r => ind_neg (h r))
        rw [e, Ex_const hp1 hqs]
      simp [this]
    by_cases hJ : Jset κ z ρ P = ∅
    · -- no candidate leaf: every term is at most sel * Bound
      have hterm : ∀ Y, sel q κ z Y * ∑ z', res p Y z z' *
          Ex p q κ n z' (fun r => ind (appears ρ P ((Y, κ z) :: r))) ≤
          sel q κ z Y * Bound p q z ρ P := by
        intro Y
        by_cases hY : Holds Y z
        · by_cases hrel : ∃ r ∈ P, (Y, κ z) ∈ closedNeighbors (G Ω T) (pathLabel ρ r)
          · rw [zero_of Y]
            · exact mul_nonneg (sel_nonneg hq hqs z Y) (Bound_nonneg hp hq z ρ P)
            · intro run h
              rcases h with ⟨hU, hP⟩ | ⟨P', hext, _⟩
              · have : [] ∈ Jset κ z ρ P := by
                  rw [mem_Jset, hP]
                  refine ⟨Finset.mem_singleton_self _, ?_, ?_⟩
                  · simp [← hU]
                  · simpa [← hU] using hY
                rw [hJ] at this; simp at this
              · rcases ext_cases ρ _ P' P hext with ⟨rfl, hfree⟩ | ⟨w, hw, hP, hl, _⟩
                · obtain ⟨r, hr, hr'⟩ := hrel
                  exact hfree r hr hr'
                · have : w ∈ Jset κ z ρ P := by
                    rw [mem_Jset, hl, hP]
                    exact ⟨Finset.mem_insert_self _ _, rfl, hY⟩
                  rw [hJ] at this; simp at this
          · push_neg at hrel
            have h1 := term_le Y 1 (by norm_num) (fun z' => by
              rw [one_mul]
              refine le_trans (Ex_mono hp hq hqs n z' _ _ (fun r _ => ind_mono ?_)) (IH z' P)
              intro h
              rcases h with ⟨hU, hP⟩ | ⟨P', hext, h'⟩
              · exfalso
                refine hrel [] (by rw [hP]; exact Finset.mem_singleton_self _) ?_
                rw [mem_closedNeighbors]; left; simp [hU]
              · rcases ext_cases ρ _ P' P hext with ⟨rfl, _⟩ | ⟨w, hw, hP, hl, _⟩
                · exact h'
                · exfalso
                  refine hrel w (by rw [hP]; exact Finset.mem_insert_self _ _) ?_
                  rw [hl, mem_closedNeighbors]; left; rfl)
            rw [one_mul, sum_res_Bound_free hp hp1 Y (κ z) z ρ P hrel] at h1
            exact h1
        · rw [sel_eq_zero z Y hY]; simp
      calc _ ≤ ∑ Y, sel q κ z Y * Bound p q z ρ P := Finset.sum_le_sum (fun Y _ => hterm Y)
        _ = Bound p q z ρ P := by rw [← Finset.sum_mul, sum_sel hqs, one_mul]
    · -- a deepest candidate node v
      have hJne : (Jset κ z ρ P).Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
      set v := deep (Jset κ z ρ P) hJne with hv
      obtain ⟨hvJ, hvmax⟩ := deep_spec (Jset κ z ρ P) hJne
      rw [← hv] at hvJ hvmax
      obtain ⟨hvP, hvk, hvY⟩ := (mem_Jset z ρ P v).1 hvJ
      set Ys := (pathLabel ρ v).1 with hYs
      have hUs : pathLabel ρ v = (Ys, κ z) := by rw [hYs, ← hvk]
      -- the key claim
      have claim : ∀ Y run, Holds Y z → appears ρ P ((Y, κ z) :: run) →
          Y = Ys ∧ (P = {[]} ∨ (ExtFacts ρ (Y, κ z) (P.erase v) P v ∧ appears ρ (P.erase v) run)) := by
        intro Y run hY h
        rcases h with ⟨hU, hP⟩ | ⟨P', hext, h'⟩
        · have hv0 : v = [] := by rw [hP] at hvP; simpa using hvP
          refine ⟨?_, Or.inl hP⟩
          rw [hYs, hv0, pathLabel_nil, ← hU]
        · rcases ext_cases ρ _ P' P hext with ⟨rfl, hfree⟩ | ⟨w, hw, hP, hl, hdeep⟩
          · exfalso
            refine hfree v hvP ?_
            rw [related_iff]; left; rw [hvk]
          · have hwJ : w ∈ Jset κ z ρ P := by
              rw [mem_Jset, hl, hP]
              exact ⟨Finset.mem_insert_self _ _, rfl, hY⟩
            have hvw : v = w := by
              by_contra hne
              have hvP' : v ∈ P' := by
                rw [hP] at hvP
                rcases Finset.mem_insert.mp hvP with h1 | h1
                · exact absurd h1 hne
                · exact h1
              have h2 := hdeep v hvP' (by rw [related_iff]; left; rw [hvk])
              have h3 := hvmax w hwJ
              omega
            subst hvw
            have hY' : Y = Ys := by rw [hYs, hl]
            have hPe : P.erase v = P' := by rw [hP]; exact Finset.erase_insert hw
            refine ⟨hY', Or.inr ⟨?_, ?_⟩⟩
            · rw [hPe]; exact ⟨hw, hP, hl, hdeep⟩
            · rw [hPe]; exact h'
      have hterm : ∀ Y, sel q κ z Y * ∑ z', res p Y z z' *
          Ex p q κ n z' (fun r => ind (appears ρ P ((Y, κ z) :: r))) ≤
          if Y = Ys then Bound p q z ρ P else 0 := by
        intro Y
        by_cases hY : Holds Y z
        · by_cases hYY : Y = Ys
          · rw [if_pos hYY]
            have hsel : sel q κ z Y ≤ q (κ z) Y := by
              have := sel_le hq hqs z Y; rwa [hold_eq_one Y z hY, mul_one] at this
            by_cases hP1 : P = {[]}
            · have hv0 : v = [] := by rw [hP1] at hvP; simpa using hvP
              have hρ : ρ = (Y, κ z) := by rw [hYY, ← hUs, hv0, pathLabel_nil]
              have hE : ∀ z', Ex p q κ n z' (fun r => ind (appears ρ P ((Y, κ z) :: r))) ≤ 1 :=
                fun z' => le_trans (Ex_mono hp hq hqs n z' _ _ (fun r _ => ind_le_one _))
                  (le_of_eq (Ex_const hp1 hqs n z' 1))
              have hF0 : ExtFacts ρ (Y, κ z) ∅ P [] :=
                ⟨by simp, by rw [hP1]; rfl, by rw [pathLabel_nil, hρ], by simp⟩
              calc _ ≤ sel q κ z Y * ∑ z', res p Y z z' * 1 :=
                    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z' _ =>
                      mul_le_mul_of_nonneg_left (hE z') (res_nonneg p hp _ _ _))) (sel_nonneg hq hqs z Y)
                _ = sel q κ z Y := by simp [sum_res p hp1]
                _ ≤ q (κ z) Y := hsel
                _ = Bound p q z ρ P := by
                  rw [Bound_ext hp ρ Y (κ z) ∅ P [] hF0 z hY]
                  simp only [wt, inodes, Finset.filter_empty, facV_empty, Finset.prod_empty, one_mul]
                  rw [Finset.prod_eq_one (fun i _ => by cases Y i <;> rfl), mul_one]
            · by_cases hF : ExtFacts ρ (Y, κ z) (P.erase v) P v
              · have h1 : sel q κ z Y * ∑ z', res p Y z z' *
                    Ex p q κ n z' (fun r => ind (appears ρ P ((Y, κ z) :: r))) ≤
                    sel q κ z Y * ∑ z', res p Y z z' * Bound p q z' ρ (P.erase v) := by
                  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z' _ =>
                    mul_le_mul_of_nonneg_left ?_ (res_nonneg p hp Y z z'))) (sel_nonneg hq hqs z Y)
                  refine le_trans (Ex_mono hp hq hqs n z' _ _ (fun r _ => ind_mono ?_)) (IH z' _)
                  intro h
                  rcases (claim Y r hY h).2 with h2 | h2
                  · exact absurd h2 hP1
                  · exact h2.2
                refine le_trans h1 ?_
                rw [Bound_ext hp ρ Y (κ z) (P.erase v) P v hF z hY, ← sum_res_Bound hp hp1]
                refine mul_le_mul_of_nonneg_right hsel ?_
                exact Finset.sum_nonneg (fun z' _ => mul_nonneg (res_nonneg p hp _ _ _)
                  (Bound_nonneg hp hq _ _ _))
              · rw [zero_of Y]
                · exact Bound_nonneg hp hq z ρ P
                · intro run h
                  rcases (claim Y run hY h).2 with h2 | h2
                  · exact hP1 h2
                  · exact hF h2.1
          · rw [if_neg hYY, zero_of Y]
            intro run h
            exact hYY (claim Y run hY h).1
        · rw [sel_eq_zero z Y hY]; simp only [zero_mul]; split_ifs
          · exact Bound_nonneg hp hq z ρ P
          · exact le_rfl
      calc _ ≤ ∑ Y, (if Y = Ys then Bound p q z ρ P else 0) := Finset.sum_le_sum (fun Y _ => hterm Y)
        _ = Bound p q z ρ P := by simp

end Main


section Final

theorem count_take_lt {α : Type} [DecidableEq α] (run : List α) (t t' : ℕ) (htt : t < t')
    (ht : t < run.length) : (run.take t).count run[t] < (run.take t').count run[t] := by
  have e : run.take t' = run.take t ++ (run.drop t).take (t' - t) := by
    rw [← List.take_add]; congr 1; omega
  rw [e, List.count_append]
  have e2 : (run.drop t).take (t' - t) = run[t] :: (run.drop (t + 1)).take (t' - t - 1) := by
    rw [List.drop_eq_getElem_cons ht]
    obtain ⟨m, hm⟩ : ∃ m, t' - t = m + 1 := ⟨t' - t - 1, by omega⟩
    rw [hm, List.take_succ_cons]; simp
  rw [e2, List.count_cons_self]
  omega

theorem length_le_count (n : ℕ) (run : List (Lab Ω T)) (hrun : run.length ≤ n) :
    (run.length : ℝ) ≤ ∑ x : (Σ ℓ : Lab Ω T, WitnessTree (G Ω T) (n + 1) ℓ),
      ind (appears x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) run) := by
  classical
  let f : Fin run.length → (Σ ℓ : Lab Ω T, WitnessTree (G Ω T) (n + 1) ℓ) := fun t =>
    ⟨run[t], pathsToTree (G Ω T) (n + 1) run[t] (historyWitness (G Ω T) run[t] (run.take t))
      (historyWitness_proper _ _ _)
      (fun r hr => by
        have := historyWitness_depth (G Ω T) run[t] (run.take t) r hr
        have h2 : (run.take t).length ≤ t := List.length_take_le _ _
        have h3 := t.2
        omega)⟩
  have hfP : ∀ t, witnessPaths (G Ω T) (n + 1) (f t).1 (f t).2 =
      historyWitness (G Ω T) run[t] (run.take t) := by
    intro t; simp only [f]; exact witnessPaths_pathsToTree _ _ _ _ _ _
  set S := Finset.univ.filter (fun x : (Σ ℓ : Lab Ω T, WitnessTree (G Ω T) (n + 1) ℓ) =>
    appears x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) run) with hS
  have hsum : ∑ x : (Σ ℓ : Lab Ω T, WitnessTree (G Ω T) (n + 1) ℓ),
      ind (appears x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) run) = S.card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs with h
    · rw [ind_pos h]; simp
    · rw [ind_neg h]
  rw [hsum]
  have hinj : Function.Injective f := by
    intro t t' h
    have h1 : ((f t).1, witnessPaths (G Ω T) (n + 1) (f t).1 (f t).2) =
        ((f t').1, witnessPaths (G Ω T) (n + 1) (f t').1 (f t').2) := by rw [h]
    rw [hfP, hfP] at h1
    simp only [f, Prod.mk.injEq] at h1
    obtain ⟨hl, hw⟩ := h1
    simp only [Fin.getElem_fin] at hl hw
    by_contra hne
    have hne' : (t : ℕ) ≠ t' := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
    · have := count_take_lt run t t' hlt t.2
      rw [← hl] at hw
      exact historyWitness_ne_of_root_count_ne (G Ω T) run[(t : ℕ)] _ _ (by omega) hw
    · have := count_take_lt run t' t hlt t'.2
      rw [hl] at hw
      exact historyWitness_ne_of_root_count_ne (G Ω T) run[(t' : ℕ)] _ _ (by omega) hw
  have hcard : Fintype.card (Fin run.length) ≤ S.card := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn f (fun t _ => ?_) (fun a _ b _ h => hinj h)
    rw [hS, Finset.coe_filter]
    simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and]
    rw [hfP]
    exact appears_history run t t.2
  simp only [Fintype.card_fin] at hcard
  exact_mod_cast hcard

theorem partition_le (p : ∀ i, Ω i → ℝ) (q : T → (∀ i, Option (Ω i)) → ℝ)
    (hp : ∀ i ω, 0 < p i ω) (hq : ∀ k Y, 0 ≤ q k Y)
    (μ : T → (∀ i, Option (Ω i)) → ℝ) (hμ : ∀ k Y, 0 ≤ μ k Y)
    (hcrit : ∀ k Y, (∏ i, (Y i).elim 1 (p i)) * q k Y *
      ∏ ℓ ∈ Finset.univ.filter (fun ℓ : (∀ i, Option (Ω i)) × T =>
        ℓ.2 = k ∨ ∃ i, (Y i).isSome ∧ (ℓ.1 i).isSome), (1 + μ ℓ.2 ℓ.1) ≤ μ k Y) :
    ∀ (h : ℕ) (ℓ : Lab Ω T), witnessPartition (G Ω T) (pw p q) h ℓ ≤ μ ℓ.2 ℓ.1
  | 0, ℓ => by rw [witnessPartition_zero]; exact hμ _ _
  | h + 1, ℓ => by
    rw [witnessPartition_succ]
    have hcl : closedNeighbors (G Ω T) ℓ = Finset.univ.filter (fun ℓ' : (∀ i, Option (Ω i)) × T =>
        ℓ'.2 = ℓ.2 ∨ ∃ i, (ℓ.1 i).isSome ∧ (ℓ'.1 i).isSome) := by
      ext ℓ'; rw [related_iff]; simp
    rw [hcl]
    refine le_trans ?_ (hcrit ℓ.2 ℓ.1)
    have hpw : pw p q ℓ = (∏ i, (ℓ.1 i).elim 1 (p i)) * q ℓ.2 ℓ.1 := rfl
    rw [hpw]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun j _ => ?_) (fun j _ => ?_))
      (by rw [← hpw]; exact pw_nonneg hp hq ℓ)
    · linarith [witnessPartition_nonneg (G Ω T) (pw p q) (fun x => pw_nonneg hp hq x) h j]
    · linarith [partition_le p q hp hq μ hμ hcrit h j]

end Final

end PRAcore

open PRAcore in
theorem solution {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
    (Ω : I → Type) [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp : ∀ i ω, 0 < p i ω) (hp1 : ∀ i, ∑ ω, p i ω = 1)
    (bad : T → (∀ i, Ω i) → Prop)
    (q : T → (∀ i, Option (Ω i)) → ℝ) (hq : ∀ k Y, 0 ≤ q k Y)
    (hhit : ∀ k z, bad k z →
      1 ≤ ∑ Y, q k Y * ∏ i, (Y i).elim 1 (fun ω => if z i = ω then 1 else 0))
    (μ : T → (∀ i, Option (Ω i)) → ℝ) (hμ : ∀ k Y, 0 ≤ μ k Y)
    (hcrit : ∀ k Y, (∏ i, (Y i).elim 1 (p i)) * q k Y *
      ∏ ℓ ∈ Finset.univ.filter (fun ℓ : (∀ i, Option (Ω i)) × T =>
        ℓ.2 = k ∨ ∃ i, (Y i).isSome ∧ (ℓ.1 i).isSome), (1 + μ ℓ.2 ℓ.1) ≤ μ k Y) :
    ∃ z : ∀ i, Ω i, ∀ k, ¬ bad k z := by
  by_contra hno
  push_neg at hno
  choose κ hκ using hno
  have hqs : ∀ z, 1 ≤ qs q κ z := fun z => hhit (κ z) z (hκ z)
  set M := ∑ ℓ : Lab Ω T, μ ℓ.2 ℓ.1 with hM
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M < n := exists_nat_gt M
  -- initial distribution
  have hπ : ∑ z0 : (∀ i, Ω i), ∏ i, p i (z0 i) = 1 := by
    rw [← Fintype.prod_sum (fun i ω => p i ω)]
    exact Finset.prod_eq_one (fun i _ => hp1 i)
  have hπ0 : ∀ z0 : (∀ i, Ω i), 0 ≤ ∏ i, p i (z0 i) :=
    fun z0 => Finset.prod_nonneg (fun i _ => (hp i _).le)
  have key : ∀ z0 : (∀ i, Ω i), (n : ℝ) ≤ ∑ x : (Σ ℓ : Lab Ω T, WitnessTree (G Ω T) (n + 1) ℓ),
      Bound p q z0 x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) := by
    intro z0
    rw [← Ex_length hp1 hqs n z0]
    refine le_trans (Ex_mono hp hq hqs n z0 _ _ (fun r hr => length_le_count n r hr)) ?_
    rw [Ex_sum]
    exact Finset.sum_le_sum (fun x _ => appear_bound hp hp1 hq hqs x.1 n z0 _)
  have h1 : (n : ℝ) ≤ ∑ z0 : (∀ i, Ω i), (∏ i, p i (z0 i)) *
      ∑ x : (Σ ℓ : Lab Ω T, WitnessTree (G Ω T) (n + 1) ℓ),
        Bound p q z0 x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) := by
    calc (n : ℝ) = ∑ z0 : (∀ i, Ω i), (∏ i, p i (z0 i)) * n := by rw [← Finset.sum_mul, hπ, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun z0 _ => mul_le_mul_of_nonneg_left (key z0) (hπ0 z0))
  have h2 : ∀ x : (Σ ℓ : Lab Ω T, WitnessTree (G Ω T) (n + 1) ℓ),
      ∑ z0 : (∀ i, Ω i), (∏ i, p i (z0 i)) * Bound p q z0 x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) =
        witnessWeight (G Ω T) (pw p q) (n + 1) x.1 x.2 := by
    intro x
    rw [witnessWeight_eq_prod_paths]
    unfold Bound
    have e : ∀ z0 : (∀ i, Ω i), (∏ i, p i (z0 i)) * (wt p q x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) *
        ∏ i, facV p x.1 i (inodes x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) i) (z0 i)) =
        wt p q x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) * ∏ i, (p i (z0 i) *
          facV p x.1 i (inodes x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) i) (z0 i)) := by
      intro z0; rw [Finset.prod_mul_distrib]; ring
    simp_rw [e]
    rw [← Finset.mul_sum, ← Fintype.prod_sum (fun i ω => p i ω *
      facV p x.1 i (inodes x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) i) ω)]
    rw [Finset.prod_eq_one (fun i _ => sum_facV hp hp1 _ _ _), mul_one]
    rfl
  have h3 : ∑ z0 : (∀ i, Ω i), (∏ i, p i (z0 i)) *
      ∑ x : (Σ ℓ : Lab Ω T, WitnessTree (G Ω T) (n + 1) ℓ),
        Bound p q z0 x.1 (witnessPaths (G Ω T) (n + 1) x.1 x.2) ≤ M := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [h2]
    rw [Fintype.sum_sigma]
    refine Finset.sum_le_sum (fun ℓ _ => ?_)
    exact partition_le p q hp hq μ hμ hcrit (n + 1) ℓ
  linarith
