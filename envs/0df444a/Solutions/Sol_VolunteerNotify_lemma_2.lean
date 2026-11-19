-- Prove2me | solution 1 for VolunteerNotify.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T20:40:19.130988+00:00
-- url     : https://prove2.me/submissions/ffa9e0d4-95bf-4569-acac-fb1b250c1fba

import Mathlib
import Definitions.Def_VolunteerNotify_IsDP
import Definitions.Def_VolunteerNotify_Process

open MeasureTheory

set_option linter.unusedSectionVars false

namespace VNL2

open MeasureTheory ProbabilityTheory

/-! ### Bounded real functions -/

/-- `F` is bounded. -/
def Bdd {α : Type*} (F : α → ℝ) : Prop := ∃ C, ∀ a, |F a| ≤ C

lemma Bdd.const {α : Type*} (c : ℝ) : Bdd (fun _ : α => c) := ⟨|c|, fun _ => le_rfl⟩

lemma Bdd.add {α : Type*} {F G : α → ℝ} (hF : Bdd F) (hG : Bdd G) : Bdd (fun a => F a + G a) := by
  obtain ⟨C, hC⟩ := hF; obtain ⟨D, hD⟩ := hG
  exact ⟨C + D, fun a => (abs_add_le _ _).trans (add_le_add (hC a) (hD a))⟩

lemma Bdd.sub {α : Type*} {F G : α → ℝ} (hF : Bdd F) (hG : Bdd G) : Bdd (fun a => F a - G a) := by
  obtain ⟨C, hC⟩ := hF; obtain ⟨D, hD⟩ := hG
  exact ⟨C + D, fun a => (abs_sub _ _).trans (add_le_add (hC a) (hD a))⟩

lemma Bdd.mul {α : Type*} {F G : α → ℝ} (hF : Bdd F) (hG : Bdd G) : Bdd (fun a => F a * G a) := by
  obtain ⟨C, hC⟩ := hF; obtain ⟨D, hD⟩ := hG
  refine ⟨C * D, fun a => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC a) (hD a) (abs_nonneg _) ((abs_nonneg _).trans (hC a))

lemma Bdd.comp {α β : Type*} {F : β → ℝ} (hF : Bdd F) (h : α → β) : Bdd (fun a => F (h a)) := by
  obtain ⟨C, hC⟩ := hF
  exact ⟨C, fun a => hC _⟩

lemma Bdd.ite {α : Type*} (p : α → Prop) [DecidablePred p] {F G : α → ℝ} (hF : Bdd F)
    (hG : Bdd G) : Bdd (fun a => if p a then F a else G a) := by
  obtain ⟨C, hC⟩ := hF; obtain ⟨D, hD⟩ := hG
  refine ⟨max C D, fun a => ?_⟩
  dsimp only
  split_ifs
  · exact (hC a).trans (le_max_left _ _)
  · exact (hD a).trans (le_max_right _ _)

lemma Bdd.sum {α κ : Type*} (s : Finset κ) {F : κ → α → ℝ} (hF : ∀ k ∈ s, Bdd (F k)) :
    Bdd (fun a => ∑ k ∈ s, F k a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Bdd.const (α := α) 0
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hF k (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

lemma Bdd.prod {α κ : Type*} (s : Finset κ) {F : κ → α → ℝ} (hF : ∀ k ∈ s, Bdd (F k)) :
    Bdd (fun a => ∏ k ∈ s, F k a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Bdd.const (α := α) 1
  | insert k s hk ih =>
    simp only [Finset.prod_insert hk]
    exact (hF k (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-! ### Expectations of functions of independent `ℕ`-valued variables -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℕ) (hX : ∀ i, Measurable (X i))

/-- The `{0,1}`-indicator of `a i = m`. -/
def ind (i : ι) (m : ℕ) (a : ι → ℕ) : ℝ := if a i = m then 1 else 0

lemma ind_nonneg (i : ι) (m : ℕ) (a : ι → ℕ) : 0 ≤ ind i m a := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (i : ι) (m : ℕ) (a : ι → ℕ) : ind i m a ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma bdd_ind (i : ι) (m : ℕ) : Bdd (ind i m) :=
  ⟨1, fun a => by rw [abs_le]; constructor <;> linarith [ind_nonneg i m a, ind_le_one i m a]⟩

lemma dep_ind (i : ι) (m : ℕ) : DependsOn (ind i m) (({i} : Finset ι) : Set ι) := by
  intro x y h
  unfold ind
  rw [h i (by simp)]

include hX in
lemma aesm (F : (ι → ℕ) → ℝ) : AEStronglyMeasurable (fun ω => F (fun i => X i ω)) μ :=
  ((measurable_of_countable F).comp (measurable_pi_lambda _ hX)).aestronglyMeasurable

include hX in
lemma integrable_of_bdd {F : (ι → ℕ) → ℝ} (hF : Bdd F) :
    Integrable (fun ω => F (fun i => X i ω)) μ := by
  obtain ⟨C, hC⟩ := hF
  exact (integrable_const C).mono' (aesm X hX F) (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC _)

include hX in
lemma integral_ind (i : ι) (m : ℕ) :
    ∫ ω, ind i m (fun j => X j ω) ∂μ = μ.real (X i ⁻¹' {m}) := by
  have : (fun ω => ind i m (fun j => X j ω)) = (X i ⁻¹' {m}).indicator 1 := by
    ext ω
    by_cases h : X i ω = m <;> simp [ind, h, Set.indicator]
  rw [this, integral_indicator_one ((hX i) (measurableSet_singleton m))]

include hX in
/-- Functions of disjoint sets of coordinates are uncorrelated. -/
lemma integral_mul_dep (hind : iIndepFun X μ) (A B : Finset ι) (hAB : Disjoint A B)
    (F G : (ι → ℕ) → ℝ) (hF : DependsOn F (A : Set ι)) (hG : DependsOn G (B : Set ι)) :
    ∫ ω, F (fun i => X i ω) * G (fun i => X i ω) ∂μ =
      (∫ ω, F (fun i => X i ω) ∂μ) * ∫ ω, G (fun i => X i ω) ∂μ := by
  set extA : (A → ℕ) → (ι → ℕ) := fun y i => if h : i ∈ A then y ⟨i, h⟩ else 0 with hextA
  set extB : (B → ℕ) → (ι → ℕ) := fun y i => if h : i ∈ B then y ⟨i, h⟩ else 0 with hextB
  have hFA : ∀ ω, F (fun i => X i ω) = (F ∘ extA) (fun i : A => X i ω) := by
    intro ω
    apply hF
    intro i hi
    simp [hextA, Finset.mem_coe.1 hi]
  have hGB : ∀ ω, G (fun i => X i ω) = (G ∘ extB) (fun i : B => X i ω) := by
    intro ω
    apply hG
    intro i hi
    simp [hextB, Finset.mem_coe.1 hi]
  simp only [hFA, hGB]
  have hI := (hind.indepFun_finset A B hAB hX).comp (measurable_of_countable (F ∘ extA))
    (measurable_of_countable (G ∘ extB))
  exact hI.integral_fun_mul_eq_mul_integral
    ((measurable_of_countable (F ∘ extA)).comp
      (measurable_pi_lambda _ fun i => hX i)).aestronglyMeasurable
    ((measurable_of_countable (G ∘ extB)).comp
      (measurable_pi_lambda _ fun i => hX i)).aestronglyMeasurable

include hX in
/-- Functions of pairwise disjoint sets of coordinates: the expectation of the product is the
product of the expectations. -/
lemma integral_prod_dep (hind : iIndepFun X μ) {κ : Type*} [DecidableEq κ] (K : Finset κ)
    (D : κ → Finset ι) (hD : ∀ k ∈ K, ∀ j ∈ K, k ≠ j → Disjoint (D k) (D j))
    (F : κ → (ι → ℕ) → ℝ) (hF : ∀ k ∈ K, DependsOn (F k) (D k : Set ι)) :
    ∫ ω, ∏ k ∈ K, F k (fun i => X i ω) ∂μ = ∏ k ∈ K, ∫ ω, F k (fun i => X i ω) ∂μ := by
  induction K using Finset.induction_on with
  | empty => simp
  | insert k K hk ih =>
    simp only [Finset.prod_insert hk]
    rw [← ih (fun a ha b hb hab => hD a (Finset.mem_insert_of_mem ha) b
      (Finset.mem_insert_of_mem hb) hab) (fun j hj => hF j (Finset.mem_insert_of_mem hj))]
    refine integral_mul_dep X hX hind (D k) (K.biUnion D) ?_ (F k)
      (fun a => ∏ j ∈ K, F j a) (hF k (Finset.mem_insert_self k K)) ?_
    · rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hD k (Finset.mem_insert_self k K) j (Finset.mem_insert_of_mem hj)
        (fun h => hk (h ▸ hj))
    · intro x y hxy
      refine Finset.prod_congr rfl fun j hj =>
        hF j (Finset.mem_insert_of_mem hj) fun i hi => hxy i ?_
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
      exact ⟨j, hj, hi⟩

end Generic

end VNL2
namespace VNL2

open VolunteerNotify MeasureTheory ProbabilityTheory

section Domain

variable {V S T : ℕ}

/-- The period of a primitive. -/
def time : Prim V S T → ℕ
  | .arrival t => t
  | .notify _ _ t => t
  | .respond _ _ t => t
  | .gap _ t => t

/-- Primitives of the periods before `n`. -/
def past (n : ℕ) : Finset (Prim V S T) := Finset.univ.filter fun i => time i < n

/-- Primitives of period `n`. -/
def pres (n : ℕ) : Finset (Prim V S T) := Finset.univ.filter fun i => time i = n

lemma disjoint_past_pres (n : ℕ) : Disjoint (past n : Finset (Prim V S T)) (pres n) := by
  rw [past, pres, Finset.disjoint_filter]
  intro i _ h1 h2
  omega

/-- `b_v(n)` only reads the primitives of periods before `n`. -/
lemma nextActive_congr (v : Fin V) (n : ℕ) : ∀ a a' : Prim V S T → ℕ,
    (∀ i, time i < n → a i = a' i) → nextActive a v n = nextActive a' v n := by
  induction n with
  | zero => intro a a' _; simp [nextActive]
  | succ n ih =>
    intro a a' h
    have ih' := ih a a' fun i hi => h i (by omega)
    by_cases hT : n < T
    · have e1 : a (.arrival ⟨n, hT⟩) = a' (.arrival ⟨n, hT⟩) := h _ (by simp [time])
      have e2 : ∀ s, a (.notify v s ⟨n, hT⟩) = a' (.notify v s ⟨n, hT⟩) :=
        fun s => h _ (by simp [time])
      have e3 : a (.gap v ⟨n, hT⟩) = a' (.gap v ⟨n, hT⟩) := h _ (by simp [time])
      have hN : IsNotified a v ⟨n, hT⟩ ↔ IsNotified a' v ⟨n, hT⟩ := by
        simp only [IsNotified, arrivalOf, e1, e2]
      simp only [nextActive, dif_pos hT]
      rw [e3]
      by_cases hc : nextActive a v n ≤ n ∧ IsNotified a v ⟨n, hT⟩
      · rw [if_pos hc, if_pos (by rwa [← ih', ← hN])]
      · rw [if_neg hc, if_neg (by rwa [← ih', ← hN]), ih']
    · simp only [nextActive, dif_neg hT, ih']

open scoped Classical in
lemma nextActive_succ (a : Prim V S T → ℕ) (v : Fin V) (t : Fin T) :
    nextActive a v ((t : ℕ) + 1) =
      if nextActive a v t ≤ t ∧ IsNotified a v t then (t : ℕ) + a (.gap v t)
      else nextActive a v t := by
  simp only [nextActive, dif_pos t.isLt, Fin.eta]

/-- The indicator that `v` is active at period `n`. -/
noncomputable def act (v : Fin V) (n : ℕ) (a : Prim V S T → ℕ) : ℝ :=
  if nextActive a v n ≤ n then 1 else 0

lemma dep_act (v : Fin V) (n : ℕ) :
    DependsOn (act (S := S) (T := T) v n) ((past n : Finset (Prim V S T)) : Set _) := by
  intro x y h
  unfold act
  rw [nextActive_congr v n x y fun i hi => h i (by simp [past, hi])]

lemma bdd_act (v : Fin V) (n : ℕ) : Bdd (act (S := S) (T := T) v n) :=
  ⟨1, fun a => by unfold act; split_ifs <;> norm_num⟩

lemma arr_iff (a : Prim V S T → ℕ) (t : Fin T) (s : Fin S) :
    a (.arrival t) = (s : ℕ) + 1 ↔ arrivalOf a t = some s := by
  unfold arrivalOf
  generalize a (.arrival t) = m
  rcases m with _ | m
  · simp
  · by_cases hm : m < S
    · simp [hm, Fin.ext_iff, eq_comm]
    · have := s.isLt
      simp only [hm, dite_false, reduceCtorEq, iff_false]
      omega

lemma ind_arr (a : Prim V S T → ℕ) (t : Fin T) (s : Fin S) :
    ind (.arrival t) ((s : ℕ) + 1) a = if arrivalOf a t = some s then 1 else 0 := by
  unfold ind
  simp only [arr_iff]

lemma sum_arr_none {a : Prim V S T → ℕ} {t : Fin T} (h : arrivalOf a t = none)
    (c : Fin S → ℝ) : ∑ s : Fin S, ind (.arrival t) ((s : ℕ) + 1) a * c s = 0 := by
  simp [ind_arr, h]

lemma sum_arr_some {a : Prim V S T → ℕ} {t : Fin T} {s₀ : Fin S}
    (h : arrivalOf a t = some s₀) (c : Fin S → ℝ) :
    ∑ s : Fin S, ind (.arrival t) ((s : ℕ) + 1) a * c s = c s₀ := by
  simp [ind_arr, h]

/-- The indicator that `v` is notified at `t`, written through the primitives of `t`. -/
noncomputable def notif (v : Fin V) (t : Fin T) (a : Prim V S T → ℕ) : ℝ :=
  ∑ s : Fin S, ind (.arrival t) ((s : ℕ) + 1) a * ind (.notify v s t) 1 a

open scoped Classical in
lemma notif_eq (v : Fin V) (t : Fin T) (a : Prim V S T → ℕ) :
    notif v t a = if IsNotified a v t then 1 else 0 := by
  unfold notif IsNotified
  rcases h : arrivalOf a t with _ | s₀
  · rw [sum_arr_none h]
    simp
  · rw [sum_arr_some h]
    simp [ind]

/-! ### Expectations on the process -/

variable {I : Instance V S T} {w : Decision V S T} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The expectation of a function of the primitives. -/
noncomputable def ex (P : Process I w μ) (F : (Prim V S T → ℕ) → ℝ) : ℝ :=
  ∫ ω, F (fun i => P.prim i ω) ∂μ

lemma ex_const (P : Process I w μ) (c : ℝ) : ex P (fun _ => c) = c := by
  simp [ex]

lemma ex_add (P : Process I w μ) {F G : (Prim V S T → ℕ) → ℝ} (hF : Bdd F) (hG : Bdd G) :
    ex P (fun a => F a + G a) = ex P F + ex P G :=
  integral_add (integrable_of_bdd _ P.measurable_prim hF)
    (integrable_of_bdd _ P.measurable_prim hG)

lemma ex_sub (P : Process I w μ) {F G : (Prim V S T → ℕ) → ℝ} (hF : Bdd F) (hG : Bdd G) :
    ex P (fun a => F a - G a) = ex P F - ex P G :=
  integral_sub (integrable_of_bdd _ P.measurable_prim hF)
    (integrable_of_bdd _ P.measurable_prim hG)

lemma ex_mul_const (P : Process I w μ) (F : (Prim V S T → ℕ) → ℝ) (c : ℝ) :
    ex P (fun a => F a * c) = ex P F * c :=
  integral_mul_const c _

lemma ex_sum (P : Process I w μ) {κ : Type*} (s : Finset κ) {F : κ → (Prim V S T → ℕ) → ℝ}
    (hF : ∀ k ∈ s, Bdd (F k)) : ex P (fun a => ∑ k ∈ s, F k a) = ∑ k ∈ s, ex P (F k) :=
  integral_finsetSum s fun k hk => integrable_of_bdd _ P.measurable_prim (hF k hk)

lemma ex_mono (P : Process I w μ) {F G : (Prim V S T → ℕ) → ℝ} (hF : Bdd F) (hG : Bdd G)
    (h : ∀ a, F a ≤ G a) : ex P F ≤ ex P G :=
  integral_mono (integrable_of_bdd _ P.measurable_prim hF)
    (integrable_of_bdd _ P.measurable_prim hG) fun ω => h _

lemma ex_mul_dep (P : Process I w μ) (A B : Finset (Prim V S T)) (hAB : Disjoint A B)
    {F G : (Prim V S T → ℕ) → ℝ} (hF : DependsOn F (A : Set _)) (hG : DependsOn G (B : Set _)) :
    ex P (fun a => F a * G a) = ex P F * ex P G :=
  integral_mul_dep _ P.measurable_prim P.indep A B hAB F G hF hG

lemma ex_prod_dep (P : Process I w μ) {κ : Type*} [DecidableEq κ] (K : Finset κ)
    (D : κ → Finset (Prim V S T)) (hD : ∀ k ∈ K, ∀ j ∈ K, k ≠ j → Disjoint (D k) (D j))
    (F : κ → (Prim V S T → ℕ) → ℝ) (hF : ∀ k ∈ K, DependsOn (F k) (D k : Set _)) :
    ex P (fun a => ∏ k ∈ K, F k a) = ∏ k ∈ K, ex P (F k) :=
  integral_prod_dep _ P.measurable_prim P.indep K D hD F hF

lemma ex_ind (P : Process I w μ) (i : Prim V S T) (m : ℕ) :
    ex P (ind i m) = primMass I w i m := by
  unfold ex
  rw [integral_ind _ P.measurable_prim, P.law]

lemma ex_arr (P : Process I w μ) (t : Fin T) (s : Fin S) :
    ex P (ind (.arrival t) ((s : ℕ) + 1)) = I.lam s t := by
  rw [ex_ind]
  simp [primMass, s.isLt]

lemma ex_notify (P : Process I w μ) (u : Fin V) (s : Fin S) (t : Fin T) :
    ex P (ind (.notify u s t) 1) = w u s t := by
  rw [ex_ind]
  simp [primMass, coinMass]

lemma ex_respond (P : Process I w μ) (u : Fin V) (s : Fin S) (t : Fin T) :
    ex P (ind (.respond u s t) 1) = I.p u s := by
  rw [ex_ind]
  simp [primMass, coinMass]

lemma ex_gap (P : Process I w μ) (u : Fin V) (t : Fin T) (k : ℕ) :
    ex P (ind (.gap u t) k) = I.g k := by
  rw [ex_ind]
  simp [primMass]

end Domain

end VNL2
namespace VNL2

open VolunteerNotify MeasureTheory ProbabilityTheory

section Main

variable {V S T : ℕ}

lemma sum_Ioi_eq (t : Fin T) (F : ℕ → ℝ) :
    ∑ τ ∈ Finset.Ioi t, F τ = ∑ k ∈ Finset.range (T - 1 - t), F (t + 1 + k) := by
  symm
  refine Finset.sum_bij (fun k hk => (⟨(t : ℕ) + 1 + k, by
      have := Finset.mem_range.1 hk; omega⟩ : Fin T)) ?_ ?_ ?_ ?_
  · intro k _
    simp only [Finset.mem_Ioi, Fin.lt_def]
    omega
  · intro a _ b _ h
    simp only [Fin.mk.injEq] at h
    omega
  · intro τ hτ
    have := Fin.lt_def.1 (Finset.mem_Ioi.1 hτ)
    refine ⟨(τ : ℕ) - t - 1, Finset.mem_range.2 (by omega), ?_⟩
    ext
    simp only
    omega
  · intro k _
    rfl

/-- `J_{v,m+1}` (0-based `m`) on all of `ℕ`, zero beyond `T + 1`. -/
noncomputable def Jh (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (m : ℕ) : ℝ :=
  if h : m < T + 1 then J v ⟨m, h⟩ else 0

lemma Jh_ge (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (hJ : J v (Fin.last T) = 0) (m : ℕ)
    (hm : T ≤ m) : Jh J v m = 0 := by
  unfold Jh
  split_ifs with h
  · have : (⟨m, h⟩ : Fin (T + 1)) = Fin.last T := by ext; simp; omega
    rw [this, hJ]
  · rfl

lemma bdd_Jh (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) : Bdd (Jh J v) := by
  refine ⟨∑ i, |J v i|, fun m => ?_⟩
  unfold Jh
  split_ifs with h
  · exact Finset.single_le_sum (f := fun i => |J v i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ _)
  · simp only [abs_zero]
    exact Finset.sum_nonneg fun i _ => abs_nonneg _

lemma Jh_castSucc (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (t : Fin T) :
    J v t.castSucc = Jh J v t := by
  unfold Jh
  rw [dif_pos (by omega)]
  rfl

lemma Jh_succ (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (t : Fin T) :
    J v t.succ = Jh J v (t + 1) := by
  unfold Jh
  rw [dif_pos (by omega)]
  rfl

/-- The value of the state at the start of period `n`: `J` at the next active period. -/
noncomputable def val (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (n : ℕ)
    (a : Prim V S T → ℕ) : ℝ :=
  Jh J v (max (nextActive a v n) n)

/-- The change of the value over an active period `t`. -/
noncomputable def Hn (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (t : Fin T)
    (a : Prim V S T → ℕ) : ℝ :=
  Jh J v (t + 1) - Jh J v t +
    notif v t a * (Jh J v (max (t + a (.gap v t)) (t + 1)) - Jh J v (t + 1))

lemma val_succ (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (t : Fin T) (a : Prim V S T → ℕ) :
    val J v (t + 1) a = val J v t a + act v t a * Hn J v t a := by
  classical
  unfold val act Hn
  rw [notif_eq, nextActive_succ]
  by_cases hA : nextActive a v t ≤ t
  · by_cases hN : IsNotified a v t
    · rw [if_pos ⟨hA, hN⟩, if_pos hA, if_pos hN, max_eq_right hA]
      ring
    · rw [if_neg (fun h => hN h.2), if_pos hA, if_neg hN, max_eq_right hA,
        max_eq_right (by omega : nextActive a v t ≤ t + 1)]
      ring
  · rw [if_neg (fun h => hA h.1), if_neg hA,
      max_eq_left (by omega : (t : ℕ) + 1 ≤ nextActive a v t),
      max_eq_left (by omega : (t : ℕ) ≤ nextActive a v t)]
    ring

lemma bdd_notif (v : Fin V) (t : Fin T) : Bdd (notif (S := S) v t) :=
  ⟨1, fun a => by classical rw [notif_eq]; split_ifs <;> norm_num⟩

lemma bdd_Hn (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (t : Fin T) :
    Bdd (Hn (S := S) J v t) := by
  unfold Hn
  exact ((Bdd.const _).sub (Bdd.const _)).add
    ((bdd_notif v t).mul (((bdd_Jh J v).comp _).sub (Bdd.const _)))

lemma bdd_val (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (n : ℕ) :
    Bdd (val (S := S) J v n) :=
  (bdd_Jh J v).comp _

lemma mem_pres {i : Prim V S T} {n : ℕ} (h : time i = n) :
    i ∈ ((pres n : Finset (Prim V S T)) : Set (Prim V S T)) := by
  simp [pres, h]

lemma dep_notif (v : Fin V) (t : Fin T) :
    DependsOn (notif (S := S) v t) ((pres t : Finset (Prim V S T)) : Set _) := by
  intro x y h
  unfold notif
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold ind
  rw [h _ (mem_pres rfl : Prim.arrival t ∈ _), h _ (mem_pres rfl : Prim.notify v s t ∈ _)]

lemma dep_Hn (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (t : Fin T) :
    DependsOn (Hn (S := S) J v t) ((pres t : Finset (Prim V S T)) : Set _) := by
  intro x y h
  unfold Hn
  rw [dep_notif v t h, h _ (mem_pres rfl : Prim.gap v t ∈ _)]

variable {I : Instance V S T} {w : Decision V S T} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma ex_notif (P : Process I w μ) (v : Fin V) (t : Fin T) :
    ex P (notif v t) = ∑ s, I.lam s t * w v s t := by
  unfold notif
  rw [ex_sum P _ fun s _ => (bdd_ind _ _).mul (bdd_ind _ _)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ex_mul_dep P {Prim.arrival t} {Prim.notify v s t} (by simp) (dep_ind _ _) (dep_ind _ _),
    ex_arr, ex_notify]

lemma Jh_gap_sum (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (hJ : J v (Fin.last T) = 0)
    (t : Fin T) (z : ℕ) :
    Jh J v (max (t + z) (t + 1)) = ∑ k ∈ Finset.range (T - t),
      (if z = k then (1 : ℝ) else 0) * Jh J v (max (t + k) (t + 1)) := by
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with hz
  · rfl
  · exact Jh_ge J v hJ _ (by omega)

lemma fv_eq (J : Fin V → Fin (T + 1) → ℝ) (v : Fin V) (t : Fin T) :
    ∑ k ∈ Finset.range (T - t), I.g k * Jh J v (max (t + k) (t + 1)) =
      futureValue I (J v) t := by
  unfold futureValue
  have h1 := sum_Ioi_eq t (fun n => I.g (n - t) * Jh J v n)
  simp only [Jh_castSucc]
  rw [h1]
  have hT : T - t = (T - 1 - t) + 1 := by omega
  rw [hT, Finset.sum_range_succ', I.g_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : (t : ℕ) + 1 + k - t = k + 1 := by omega
  have e2 : max ((t : ℕ) + (k + 1)) (t + 1) = t + 1 + k := by omega
  rw [e1, e2]

lemma ex_Hn {x : Decision V S T} {J : Fin V → Fin (T + 1) → ℝ} (hdp : IsDP I x w J)
    (P : Process I w μ) (v : Fin V) (t : Fin T) :
    ex P (Hn J v t) = -∑ s, I.lam s t * w v s t * reward I w v s t := by
  have hJ := hdp.terminal v
  set L : (Prim V S T → ℕ) → ℝ := fun a =>
    Jh J v (max (t + a (.gap v t)) (t + 1)) - Jh J v (t + 1) with hL
  have hbL : Bdd L := ((bdd_Jh J v).comp _).sub (Bdd.const _)
  have h1 : ex P (Hn J v t) = (Jh J v (t + 1) - Jh J v t) + ex P (fun a => notif v t a * L a) := by
    unfold Hn
    rw [ex_add P (Bdd.const _) ((bdd_notif v t).mul hbL), ex_const]
  -- The notification and the gap of period `t` are independent.
  have h2 : ex P (fun a => notif v t a * L a) = ex P (notif v t) * ex P L := by
    refine ex_mul_dep P (Finset.univ.erase (Prim.gap v t)) {Prim.gap v t} (by simp) ?_ ?_
    · intro x y h
      unfold notif
      refine Finset.sum_congr rfl fun s _ => ?_
      unfold ind
      rw [h (Prim.arrival t) (by simp), h (Prim.notify v s t) (by simp)]
    · intro x y h
      simp only [hL]
      rw [h (Prim.gap v t) (by simp)]
  have h3 : ex P L = ∑ k ∈ Finset.range (T - t), I.g k * Jh J v (max (t + k) (t + 1)) -
      Jh J v (t + 1) := by
    rw [hL, ex_sub P ((bdd_Jh J v).comp _) (Bdd.const _), ex_const]
    congr 1
    have : (fun a : Prim V S T → ℕ => Jh J v (max (t + a (.gap v t)) (t + 1))) =
        fun a => ∑ k ∈ Finset.range (T - t),
          ind (Prim.gap v t) k a * Jh J v (max (t + k) (t + 1)) := by
      funext a
      rw [Jh_gap_sum J v hJ t]
      rfl
    rw [this, ex_sum P _ fun k _ => (bdd_ind _ _).mul (Bdd.const _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ex_mul_const, ex_gap]
  rw [h1, h2, h3, ex_notif, fv_eq]
  -- The dynamic program (8) at `t`.
  have hval := hdp.value v t
  rw [Jh_castSucc J v t, Jh_succ J v t, Instance.noTask] at hval
  have e : ∑ s, I.lam s t * ((1 - w v s t) * Jh J v (t + 1) +
      w v s t * (reward I w v s t + futureValue I (J v) t)) =
      (∑ s, I.lam s t) * Jh J v (t + 1) - (∑ s, I.lam s t * w v s t) * Jh J v (t + 1) +
        (∑ s, I.lam s t * w v s t * reward I w v s t) +
        (∑ s, I.lam s t * w v s t) * futureValue I (J v) t := by
    simp only [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e] at hval
  linarith

lemma ex_val_succ {x : Decision V S T} {J : Fin V → Fin (T + 1) → ℝ} (hdp : IsDP I x w J)
    (P : Process I w μ) (v : Fin V) (t : Fin T) :
    ex P (val J v (t + 1)) =
      ex P (val J v t) - ex P (act v t) * ∑ s, I.lam s t * w v s t * reward I w v s t := by
  have : val J v ((t : ℕ) + 1) =
      fun a : Prim V S T → ℕ => val J v t a + act v t a * Hn J v t a := by
    funext a; exact val_succ J v t a
  rw [this, ex_add P (bdd_val J v t) ((bdd_act v t).mul (bdd_Hn J v t)),
    ex_mul_dep P (past t) (pres t) (disjoint_past_pres t) (dep_act v t) (dep_Hn J v t),
    ex_Hn hdp P v t]
  ring

/-- The value identity: `∑_t P(v active at t) ρ_t = J_{v,1}`. -/
lemma renewal {x : Decision V S T} {J : Fin V → Fin (T + 1) → ℝ} (hdp : IsDP I x w J)
    (P : Process I w μ) (v : Fin V) :
    ∑ t : Fin T, ex P (act v t) * ∑ s, I.lam s t * w v s t * reward I w v s t = J v 0 := by
  have hJ := hdp.terminal v
  have hstep : ∀ t : Fin T, ex P (act v t) * ∑ s, I.lam s t * w v s t * reward I w v s t =
      ex P (val J v t) - ex P (val J v ((t : ℕ) + 1)) := by
    intro t; rw [ex_val_succ hdp P v t]; ring
  simp only [hstep]
  rw [Fin.sum_univ_eq_sum_range (fun n => ex P (val J v n) - ex P (val J v (n + 1))) T,
    Finset.sum_range_sub']
  have h0 : val J v 0 = fun _ : Prim V S T → ℕ => J v 0 := by
    funext a; simp [val, nextActive, Jh]
  have hT : val J v T = fun _ : Prim V S T → ℕ => 0 := by
    funext a; exact Jh_ge J v hJ _ (le_max_right _ _)
  rw [h0, hT, ex_const, ex_const, sub_zero]

/-! ### Completions by `v` -/

/-- `v` is active, a task of type `s` arrives, `v` is notified and responds, and no `u < v` is
both notified and responding: then `v` completes the task. -/
noncomputable def Gs (v : Fin V) (s : Fin S) (t : Fin T) (a : Prim V S T → ℕ) : ℝ :=
  ind (.notify v s t) 1 a * ind (.respond v s t) 1 a *
    ∏ u ∈ Finset.Iio v, (1 - ind (.notify u s t) 1 a * ind (.respond u s t) 1 a)

noncomputable def W (v : Fin V) (t : Fin T) (a : Prim V S T → ℕ) : ℝ :=
  act v t a * ∑ s : Fin S, ind (.arrival t) ((s : ℕ) + 1) a * Gs v s t a

lemma bdd_Gs (v : Fin V) (s : Fin S) (t : Fin T) : Bdd (Gs (S := S) v s t) :=
  ((bdd_ind _ _).mul (bdd_ind _ _)).mul
    (Bdd.prod _ fun u _ => (Bdd.const _).sub ((bdd_ind _ _).mul (bdd_ind _ _)))

lemma bdd_W (v : Fin V) (t : Fin T) : Bdd (W (S := S) v t) :=
  (bdd_act v t).mul (Bdd.sum _ fun s _ => (bdd_ind _ _).mul (bdd_Gs v s t))

lemma ex_Gs (P : Process I w μ) (v : Fin V) (s : Fin S) (t : Fin T) :
    ex P (Gs v s t) = w v s t * reward I w v s t := by
  unfold Gs
  set D : Fin V → Finset (Prim V S T) := fun u => {Prim.notify u s t, Prim.respond u s t}
    with hD
  have hdisj : Disjoint ({Prim.notify v s t, Prim.respond v s t} : Finset (Prim V S T))
      ((Finset.Iio v).biUnion D) := by
    rw [Finset.disjoint_biUnion_right]
    intro u hu
    have : u ≠ v := ne_of_lt (Finset.mem_Iio.1 hu)
    simp [hD, this, this.symm]
  rw [ex_mul_dep P {Prim.notify v s t, Prim.respond v s t} ((Finset.Iio v).biUnion D) hdisj
    ?_ ?_]
  · rw [ex_mul_dep P {Prim.notify v s t} {Prim.respond v s t} (by simp) (dep_ind _ _)
      (dep_ind _ _), ex_notify, ex_respond]
    rw [ex_prod_dep P (Finset.Iio v) D ?_ _ ?_]
    · have hu : ∀ u ∈ Finset.Iio v,
          ex P (fun a => 1 - ind (Prim.notify u s t) 1 a * ind (Prim.respond u s t) 1 a) =
            1 - w u s t * I.p u s := by
        intro u _
        rw [ex_sub P (Bdd.const _) ((bdd_ind _ _).mul (bdd_ind _ _)), ex_const,
          ex_mul_dep P {Prim.notify u s t} {Prim.respond u s t} (by simp) (dep_ind _ _)
            (dep_ind _ _), ex_notify, ex_respond]
      rw [Finset.prod_congr rfl hu]
      unfold reward
      ring
    · intro k _ j _ hkj
      simp [hD, hkj, hkj.symm]
    · intro u _ x y h
      unfold ind
      dsimp only
      rw [h (Prim.notify u s t) (by simp [hD]), h (Prim.respond u s t) (by simp [hD])]
  · intro x y h
    unfold ind
    dsimp only
    rw [h (Prim.notify v s t) (by simp), h (Prim.respond v s t) (by simp)]
  · intro x y h
    refine Finset.prod_congr rfl fun u hu => ?_
    unfold ind
    have m1 : Prim.notify u s t ∈ (((Finset.Iio v).biUnion D : Finset _) : Set _) := by
      simp only [Finset.coe_biUnion, Set.mem_iUnion]; exact ⟨u, hu, by simp [hD]⟩
    have m2 : Prim.respond u s t ∈ (((Finset.Iio v).biUnion D : Finset _) : Set _) := by
      simp only [Finset.coe_biUnion, Set.mem_iUnion]; exact ⟨u, hu, by simp [hD]⟩
    rw [h _ m1, h _ m2]

end Main

end VNL2
namespace VNL2

open VolunteerNotify MeasureTheory ProbabilityTheory

section Final

variable {V S T : ℕ}

lemma dep_Gs (v : Fin V) (s : Fin S) (t : Fin T) (B : Set (Prim V S T))
    (hB : ∀ u, Prim.notify u s t ∈ B ∧ Prim.respond u s t ∈ B) : DependsOn (Gs v s t) B := by
  intro x y h
  unfold Gs ind
  rw [h _ (hB v).1, h _ (hB v).2]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [h _ (hB u).1, h _ (hB u).2]

lemma dep_Q (v : Fin V) (t : Fin T) :
    DependsOn (fun a : Prim V S T → ℕ => ∑ s : Fin S, ind (.arrival t) ((s : ℕ) + 1) a * Gs v s t a)
      ((pres t : Finset (Prim V S T)) : Set _) := by
  intro x y h
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dep_Gs v s t _ (fun u => ⟨mem_pres rfl, mem_pres rfl⟩) h]
  unfold ind
  rw [h _ (mem_pres rfl : Prim.arrival t ∈ _)]

variable {I : Instance V S T} {w : Decision V S T} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma ex_W (P : Process I w μ) (v : Fin V) (t : Fin T) :
    ex P (W v t) = ex P (act v t) * ∑ s, I.lam s t * w v s t * reward I w v s t := by
  unfold W
  rw [ex_mul_dep P (past t) (pres t) (disjoint_past_pres t) (dep_act v t) (dep_Q v t),
    ex_sum P _ fun s _ => (bdd_ind _ _).mul (bdd_Gs v s t)]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ex_mul_dep P {Prim.arrival t} (Finset.univ.erase (Prim.arrival t)) (by simp)
    (dep_ind _ _) (dep_Gs v s t _ fun u => ⟨by simp, by simp⟩), ex_arr, ex_Gs]
  ring

open scoped Classical in
lemma W_le (v : Fin V) (t : Fin T) (a : Prim V S T → ℕ) :
    W v t a ≤ if v ∈ respondents a t ∧ ∀ u < v, u ∉ respondents a t then 1 else 0 := by
  unfold W
  rcases h : arrivalOf a t with _ | s₀
  · rw [sum_arr_none h, mul_zero]
    split_ifs <;> norm_num
  · rw [sum_arr_some h]
    have hG : Gs v s₀ t a =
        if (a (.notify v s₀ t) = 1 ∧ a (.respond v s₀ t) = 1) ∧
          ∀ u ∈ Finset.Iio v, ¬(a (.notify u s₀ t) = 1 ∧ a (.respond u s₀ t) = 1)
        then 1 else 0 := by
      unfold Gs ind
      have hp : ∀ u ∈ Finset.Iio v,
          (1 - (if a (.notify u s₀ t) = 1 then (1 : ℝ) else 0) *
            (if a (.respond u s₀ t) = 1 then 1 else 0)) =
          if ¬(a (.notify u s₀ t) = 1 ∧ a (.respond u s₀ t) = 1) then 1 else 0 := by
        intro u _
        split_ifs <;> simp_all
      rw [Finset.prod_congr rfl hp, Finset.prod_ite_zero, Finset.prod_const_one]
      split_ifs <;> simp_all
    rw [hG]
    unfold act
    by_cases hA : nextActive a v t ≤ t
    · by_cases hC : (a (.notify v s₀ t) = 1 ∧ a (.respond v s₀ t) = 1) ∧
          ∀ u ∈ Finset.Iio v, ¬(a (.notify u s₀ t) = 1 ∧ a (.respond u s₀ t) = 1)
      · have hR : v ∈ respondents a t ∧ ∀ u < v, u ∉ respondents a t := by
          constructor
          · simp only [respondents, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hA, s₀, h, hC.1.1, hC.1.2⟩
          · intro u hu huR
            simp only [respondents, Finset.mem_filter, Finset.mem_univ, true_and] at huR
            obtain ⟨_, s, hs, hN, hRs⟩ := huR
            rw [h] at hs
            obtain rfl := Option.some.inj hs
            exact hC.2 u (Finset.mem_Iio.2 hu) ⟨hN, hRs⟩
        rw [if_pos hA, if_pos hC, if_pos hR]
        norm_num
      · rw [if_neg hC, mul_zero]
        split_ifs <;> norm_num
    · rw [if_neg hA, zero_mul]
      split_ifs <;> norm_num

lemma bdd_completedBy (v : Fin V) : Bdd (fun a : Prim V S T → ℕ => completedBy a v) := by
  classical
  refine ⟨T, fun a => ?_⟩
  unfold completedBy
  rw [abs_le]
  constructor
  · have : 0 ≤ ∑ t : Fin T,
        (if v ∈ respondents a t ∧ ∀ u < v, u ∉ respondents a t then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num
    linarith
  · calc _ ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t _ => by split_ifs <;> norm_num
      _ = T := by simp

end Final

end VNL2

open VolunteerNotify VNL2

theorem solution {V S T : ℕ} (I : Instance V S T) (x xt : Decision V S T)
    (J : Fin V → Fin (T + 1) → ℝ) (hx : ∀ v s t, x v s t ∈ Set.Icc (0 : ℝ) 1)
    (hdp : IsDP I x xt J) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Process I xt μ) (v : Fin V) : J v 0 ≤ contribution P v := by
  classical
  have hc : contribution P v = ex P (fun a => completedBy a v) := rfl
  rw [hc, ← renewal hdp P v]
  have hW : ∀ t : Fin T, ex P (act v t) * ∑ s, I.lam s t * xt v s t * reward I xt v s t =
      ex P (W v t) := fun t => (ex_W P v t).symm
  simp only [hW]
  rw [← ex_sum P _ fun t _ => bdd_W v t]
  refine ex_mono P (Bdd.sum _ fun t _ => bdd_W v t) (bdd_completedBy v) fun a => ?_
  unfold completedBy
  exact Finset.sum_le_sum fun t _ => W_le v t a
