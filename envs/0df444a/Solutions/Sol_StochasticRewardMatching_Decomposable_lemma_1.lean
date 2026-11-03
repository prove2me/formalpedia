-- Prove2me | solution 1 for StochasticRewardMatching.Decomposable.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:27:44.113112+00:00
-- url     : https://prove2.me/submissions/a59ef2ca-c4fb-44ff-9b74-0f9a93d2ddef

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_DynamicProgram

open scoped BigOperators
open MeasureTheory StochasticRewardMatching.Decomposable

noncomputable section

private def flipEdge {n m : ℕ} {D : Instance n m} (e : Edge D) : Outcome D ≃ Outcome D where
  toFun ω := Function.update ω e (!ω e)
  invFun ω := Function.update ω e (!ω e)
  left_inv ω := by ext f; by_cases h : f = e <;> simp [h]
  right_inv ω := by ext f; by_cases h : f = e <;> simp [h]

private lemma edgeAverage_resample {n m : ℕ} (D : Instance n m) (e : Edge D)
    (F : Outcome D → ℝ) :
    edgeAverage D (fun ω => resample D e ω F) = edgeAverage D F := by
  let restWeight (ω : Outcome D) : ℝ :=
    ∏ f ∈ Finset.univ.erase e, if ω f then D.probability f.val else 1 - D.probability f.val
  have hpw : ∀ ω : Outcome D,
      pathWeight D ω =
        (if ω e then D.probability e.val else 1 - D.probability e.val) * restWeight ω := by
    intro ω
    unfold pathWeight
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  have hrest_flip : ∀ ω : Outcome D, restWeight (flipEdge e ω) = restWeight ω := by
    intro ω
    refine Finset.prod_congr rfl fun f hf => ?_
    have hne := Finset.ne_of_mem_erase hf
    simp [flipEdge, hne]
  have hupd_flip : ∀ (ω : Outcome D) (b : Bool),
      Function.update (flipEdge e ω) e b = Function.update ω e b := by
    intro ω b
    ext f
    by_cases hf : f = e <;> simp [flipEdge, hf]
  have hres_flip : ∀ ω : Outcome D, resample D e (flipEdge e ω) F = resample D e ω F := by
    intro ω
    unfold resample
    rw [hupd_flip ω false, hupd_flip ω true]
  have hpair : ∀ ω : Outcome D,
      pathWeight D ω * resample D e ω F +
        pathWeight D (flipEdge e ω) * resample D e (flipEdge e ω) F =
      pathWeight D ω * F ω + pathWeight D (flipEdge e ω) * F (flipEdge e ω) := by
    intro ω
    rw [hres_flip ω, hpw ω, hpw (flipEdge e ω), hrest_flip ω]
    have hfe : flipEdge e ω e = !ω e := by simp [flipEdge]
    rw [hfe]
    by_cases hωe : ω e = false
    · have hu_false : Function.update ω e false = ω := by
        ext f; by_cases hf : f = e <;> simp [hf, hωe]
      have hu_true : Function.update ω e true = flipEdge e ω := by
        ext f; by_cases hf : f = e <;> simp [flipEdge, hf, hωe]
      unfold resample
      rw [hu_false, hu_true, hωe]
      simp
      ring
    · have hωe' : ω e = true := Bool.eq_true_of_not_eq_false hωe
      have hu_true : Function.update ω e true = ω := by
        ext f; by_cases hf : f = e <;> simp [hf, hωe']
      have hu_false : Function.update ω e false = flipEdge e ω := by
        ext f; by_cases hf : f = e <;> simp [flipEdge, hf, hωe']
      unfold resample
      rw [hu_true, hu_false, hωe']
      simp
      ring
  have hsum : ∑ ω : Outcome D,
      (pathWeight D ω * resample D e ω F +
        pathWeight D (flipEdge e ω) * resample D e (flipEdge e ω) F) =
    ∑ ω : Outcome D,
      (pathWeight D ω * F ω + pathWeight D (flipEdge e ω) * F (flipEdge e ω)) :=
    Finset.sum_congr rfl fun ω _ => hpair ω
  have hcomp1 : (∑ ω : Outcome D, pathWeight D (flipEdge e ω) * resample D e (flipEdge e ω) F) =
      ∑ ω : Outcome D, pathWeight D ω * resample D e ω F :=
    (flipEdge e).sum_comp (fun ω => pathWeight D ω * resample D e ω F)
  have hcomp2 : (∑ ω : Outcome D, pathWeight D (flipEdge e ω) * F (flipEdge e ω)) =
      ∑ ω : Outcome D, pathWeight D ω * F ω :=
    (flipEdge e).sum_comp (fun ω => pathWeight D ω * F ω)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcomp1, hcomp2] at hsum
  unfold edgeAverage
  linarith

private lemma sum_pathWeight_eq_one {n m : ℕ} (D : Instance n m) :
    ∑ ω : Outcome D, pathWeight D ω = 1 := by
  unfold pathWeight
  rw [← (Fintype.prod_sum (fun (f : Edge D) (b : Bool) =>
    if b then D.probability f.val else 1 - D.probability f.val))]
  refine Finset.prod_eq_one fun f _ => ?_
  simp

private lemma edgeAverage_const {n m : ℕ} (D : Instance n m) (c : ℝ) :
    edgeAverage D (fun _ => c) = c := by
  unfold edgeAverage
  rw [← Finset.sum_mul, sum_pathWeight_eq_one, one_mul]

private lemma edgeAverage_add {n m : ℕ} (D : Instance n m) (f g : Outcome D → ℝ) :
    edgeAverage D (fun ω => f ω + g ω) = edgeAverage D f + edgeAverage D g := by
  unfold edgeAverage
  simp_rw [mul_add, Finset.sum_add_distrib]

private lemma edgeAverage_const_mul {n m : ℕ} (D : Instance n m) (c : ℝ) (f : Outcome D → ℝ) :
    edgeAverage D (fun ω => c * f ω) = c * edgeAverage D f := by
  unfold edgeAverage
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => by ring

private lemma remainingArrivals_nil (n m : ℕ) :
    remainingArrivals ([] : History n m) = Finset.univ := by
  unfold remainingArrivals
  simp

private lemma remainingResources_nil (n m : ℕ) :
    remainingResources ([] : History n m) = Finset.univ := by
  unfold remainingResources
  simp

private lemma remainingArrivals_append {n m : ℕ} (h : History n m) (a : Action n m) (b : Bool) :
    remainingArrivals (h ++ [(a, b)]) = (remainingArrivals h).erase a.1 := by
  unfold remainingArrivals
  ext t
  simp only [List.map_append, List.map_cons, List.map_nil, List.toFinset_append,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_erase,
    List.mem_toFinset]
  tauto

private lemma remainingResources_append_false {n m : ℕ} (h : History n m) (a : Action n m) :
    remainingResources (h ++ [(a, false)]) = remainingResources h := by
  unfold remainingResources
  simp [List.filterMap_append]

private lemma remainingResources_append_true {n m : ℕ} (h : History n m) (a : Action n m) :
    remainingResources (h ++ [(a, true)]) = afterSuccess (remainingResources h) a := by
  unfold remainingResources afterSuccess
  cases ha : a.2 with
  | none =>
    simp [List.filterMap_append, ha]
  | some i =>
    ext j
    simp only [List.filterMap_append, List.filterMap_cons, ↓reduceIte, ha,
      List.filterMap_nil, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
      Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_erase,
      List.mem_toFinset]
    tauto

private lemma maxWithZero_nonneg (xs : List ℝ) : 0 ≤ maxWithZero xs := by
  induction xs with
  | nil => exact le_refl 0
  | cons x rest ih => exact le_max_of_le_right ih

private lemma le_maxWithZero_map {α : Type*} (f : α → ℝ) :
    ∀ (l : List α) {a : α}, a ∈ l → f a ≤ maxWithZero (l.map f)
  | [], _, ha => False.elim (List.not_mem_nil ha)
  | x :: rest, a, ha => by
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact le_max_left (f a) _
    · exact le_max_of_le_right (le_maxWithZero_map f rest hmem)

private lemma maxWithZero_map_le {α : Type*} (f : α → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    ∀ (l : List α), (∀ a ∈ l, f a ≤ c) → maxWithZero (l.map f) ≤ c
  | [], _ => hc
  | x :: rest, h =>
    max_le (h x List.mem_cons_self)
      (maxWithZero_map_le f c hc rest (fun a ha => h a (List.mem_cons_of_mem x ha)))

private lemma bestOf_eq_none_iff {α : Type} (f : α → ℝ) :
    ∀ l : List α, bestOf f l = none ↔ l = []
  | [] => by simp [bestOf]
  | a :: rest => by
    simp only [bestOf, reduceCtorEq, iff_false]
    cases bestOf f rest with
    | none => simp
    | some b =>
      dsimp only
      split_ifs <;> simp

private lemma bestOf_mem {α : Type} (f : α → ℝ) :
    ∀ {l : List α} {b : α}, bestOf f l = some b → b ∈ l
  | [], _, h => by simp [bestOf] at h
  | a :: rest, b, h => by
    dsimp [bestOf] at h
    cases hrest : bestOf f rest with
    | none =>
      rw [hrest] at h
      injection h with h
      subst h
      exact List.mem_cons_self
    | some c =>
      rw [hrest] at h
      dsimp at h
      split_ifs at h
      · injection h with h
        subst h
        exact List.mem_cons_self
      · injection h with h
        subst h
        exact List.mem_cons_of_mem a (bestOf_mem f hrest)

private lemma le_score_bestOf {α : Type} (f : α → ℝ) :
    ∀ {l : List α} {b : α}, bestOf f l = some b → ∀ x ∈ l, f x ≤ f b
  | [], _, h, _, _ => by simp [bestOf] at h
  | a :: rest, b, h, x, hx => by
    dsimp [bestOf] at h
    cases hrest : bestOf f rest with
    | none =>
      rw [hrest] at h
      injection h with h
      subst h
      have hnil : rest = [] := (bestOf_eq_none_iff f rest).mp hrest
      subst hnil
      rcases List.mem_singleton.mp hx with rfl
      exact le_refl _
    | some c =>
      rw [hrest] at h
      dsimp at h
      split_ifs at h with hca
      · injection h with h
        subst h
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact le_refl _
        · exact le_trans (le_score_bestOf f hrest x hmem) hca
      · injection h with h
        subst h
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact le_of_not_ge hca
        · exact le_score_bestOf f hrest x hmem

private lemma dp_nonneg {n m : ℕ} (D : Instance n m) (ordered : Bool) :
    ∀ (k : ℕ) (S : Finset (Fin n)) (U : Finset (Fin m)), 0 ≤ dp D ordered k S U
  | 0, _, _ => le_refl 0
  | _ + 1, _, _ => maxWithZero_nonneg _

private lemma actionProbability_bounds {n m : ℕ} (D : Instance n m) {ordered : Bool}
    {S : Finset (Fin n)} {U : Finset (Fin m)} {a : Action n m}
    (ha : a ∈ legalActions D ordered S U) :
    0 ≤ actionProbability D a ∧ actionProbability D a ≤ 1 := by
  unfold legalActions at ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  unfold actionProbability
  cases ha2 : a.2 with
  | none => constructor <;> norm_num
  | some i =>
    rw [ha2] at ha
    exact D.probability_mem (i, a.1) ha.2.2.2

private lemma actionReward_nonneg {n m : ℕ} (D : Instance n m) (a : Action n m) :
    0 ≤ actionReward D a := by
  unfold actionReward
  cases a.2 with
  | none => exact le_refl 0
  | some i => exact D.reward_nonneg i

private def dpBellman {n m : ℕ} (D : Instance n m) (ordered : Bool) (k : ℕ)
    (S : Finset (Fin n)) (U : Finset (Fin m)) (a : Action n m) : ℝ :=
  actionProbability D a * (actionReward D a + dp D ordered k (afterSuccess S a) (U.erase a.1)) +
    (1 - actionProbability D a) * dp D ordered k S (U.erase a.1)

private lemma dpBellman_nonneg {n m : ℕ} (D : Instance n m) (ordered : Bool) (k : ℕ)
    (S : Finset (Fin n)) (U : Finset (Fin m)) {a : Action n m}
    (ha : a ∈ legalActions D ordered S U) :
    0 ≤ dpBellman D ordered k S U a := by
  unfold dpBellman
  obtain ⟨hp0, hp1⟩ := actionProbability_bounds D ha
  have hr := actionReward_nonneg D a
  have h1 := dp_nonneg D ordered k (afterSuccess S a) (U.erase a.1)
  have h2 := dp_nonneg D ordered k S (U.erase a.1)
  nlinarith

private lemma pmf_sum_toReal_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    ∑ x : α, (p x).toReal = 1 := by
  have h1 := p.tsum_coe
  rw [tsum_fintype] at h1
  have h2 := ENNReal.toReal_sum (s := Finset.univ) (f := fun x => p x)
    (fun x _ => p.apply_ne_top x)
  rw [← h2, h1, ENNReal.toReal_one]

private lemma randomizedContinuation_le_dp {n m : ℕ} (D : Instance n m) (ordered : Bool)
    (π : RandPolicy n m) :
    ∀ (k : ℕ) (h : History n m),
      randomizedContinuation D ordered π k h ≤
        dp D ordered k (remainingResources h) (remainingArrivals h)
  | 0, _ => le_refl 0
  | k + 1, h => by
    unfold randomizedContinuation
    let S := remainingResources h
    let U := remainingArrivals h
    have hterm : ∀ o : Option (Action n m),
        (match o with
          | none => 0
          | some a => if a ∈ legalActions D ordered S U then
              actionProbability D a * (actionReward D a +
                randomizedContinuation D ordered π k (h ++ [(a, true)])) +
              (1 - actionProbability D a) *
                randomizedContinuation D ordered π k (h ++ [(a, false)])
            else 0) ≤ dp D ordered (k + 1) S U := by
      intro o
      cases o with
      | none => exact dp_nonneg D ordered (k + 1) S U
      | some a =>
        dsimp only
        split_ifs with ha
        · obtain ⟨hp0, hp1⟩ := actionProbability_bounds D ha
          have ih1 := randomizedContinuation_le_dp D ordered π k (h ++ [(a, true)])
          rw [remainingResources_append_true, remainingArrivals_append] at ih1
          have ih0 := randomizedContinuation_le_dp D ordered π k (h ++ [(a, false)])
          rw [remainingResources_append_false, remainingArrivals_append] at ih0
          have hle_bell :
              actionProbability D a * (actionReward D a +
                randomizedContinuation D ordered π k (h ++ [(a, true)])) +
              (1 - actionProbability D a) *
                randomizedContinuation D ordered π k (h ++ [(a, false)]) ≤
              dpBellman D ordered k S U a := by
            unfold dpBellman
            nlinarith
          have hbell_le : dpBellman D ordered k S U a ≤ dp D ordered (k + 1) S U := by
            unfold dp
            exact le_maxWithZero_map (dpBellman D ordered k S U)
              (legalActions D ordered S U).toList (Finset.mem_toList.mpr ha)
          exact le_trans hle_bell hbell_le
        · exact dp_nonneg D ordered (k + 1) S U
    calc ∑ o : Option (Action n m), (π h o).toReal * _
      _ ≤ ∑ o : Option (Action n m), (π h o).toReal * dp D ordered (k + 1) S U := by
        refine Finset.sum_le_sum fun o _ => ?_
        exact mul_le_mul_of_nonneg_left (hterm o) ENNReal.toReal_nonneg
      _ = (∑ o : Option (Action n m), (π h o).toReal) * dp D ordered (k + 1) S U := by
        rw [← Finset.sum_mul]
      _ = dp D ordered (k + 1) S U := by
        rw [pmf_sum_toReal_eq_one, one_mul]

private def pureRand {n m : ℕ} (π : DetPolicy n m) : RandPolicy n m :=
  fun h => PMF.pure (π h)

private lemma randomizedContinuation_pureRand_succ {n m : ℕ} (D : Instance n m) (ordered : Bool)
    (π : DetPolicy n m) (k : ℕ) (h : History n m) :
    randomizedContinuation D ordered (pureRand π) (k + 1) h =
      match legalize D ordered π h with
      | none => 0
      | some a =>
        actionProbability D a * (actionReward D a +
          randomizedContinuation D ordered (pureRand π) k (h ++ [(a, true)])) +
        (1 - actionProbability D a) *
          randomizedContinuation D ordered (pureRand π) k (h ++ [(a, false)]) := by
  conv_lhs => unfold randomizedContinuation pureRand
  unfold legalize
  rw [Finset.sum_eq_single (π h)]
  · simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one, one_mul]
    cases π h with
    | none => rfl
    | some a =>
      dsimp only
      split_ifs <;> rfl
  · intro o _ ho
    simp [PMF.pure_apply, ho]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

private lemma randomizedContinuation_dpPolicy {n m : ℕ} (D : Instance n m) (ordered : Bool) :
    ∀ (k : ℕ) (h : History n m),
      (remainingArrivals h).card = k →
      randomizedContinuation D ordered (pureRand (dpPolicy D ordered)) k h =
        dp D ordered k (remainingResources h) (remainingArrivals h)
  | 0, _, _ => rfl
  | k + 1, h, hcard => by
    rw [randomizedContinuation_pureRand_succ]
    let S := remainingResources h
    let U := remainingArrivals h
    have hU : U.card - 1 = k := by change (remainingArrivals h).card - 1 = k; omega
    have hpol : dpPolicy D ordered h =
        bestOf (dpBellman D ordered k S U) (legalActions D ordered S U).toList := by
      unfold dpPolicy dpBellman
      dsimp only
      rw [hU]
    have hdp_eq : dp D ordered (k + 1) S U =
        maxWithZero ((legalActions D ordered S U).toList.map (dpBellman D ordered k S U)) := rfl
    unfold legalize
    rw [hpol]
    cases hbest : bestOf (dpBellman D ordered k S U) (legalActions D ordered S U).toList with
    | none =>
      have hnil : (legalActions D ordered S U).toList = [] :=
        (bestOf_eq_none_iff _ _).mp hbest
      rw [hdp_eq, hnil]
      simp [maxWithZero]
    | some a =>
      have ha_list : a ∈ (legalActions D ordered S U).toList := bestOf_mem _ hbest
      have ha : a ∈ legalActions D ordered S U := Finset.mem_toList.mp ha_list
      have ha1 : a.1 ∈ U := by
        unfold legalActions at ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ha.1
      have hcard_erase : (U.erase a.1).card = k := by
        rw [Finset.card_erase_of_mem ha1]
        exact hU
      have ih1 := randomizedContinuation_dpPolicy D ordered k (h ++ [(a, true)])
        (by rw [remainingArrivals_append]; exact hcard_erase)
      have ih0 := randomizedContinuation_dpPolicy D ordered k (h ++ [(a, false)])
        (by rw [remainingArrivals_append]; exact hcard_erase)
      rw [remainingResources_append_true, remainingArrivals_append] at ih1
      rw [remainingResources_append_false, remainingArrivals_append] at ih0
      dsimp only
      rw [if_pos ha]
      dsimp only
      rw [ih1, ih0, hdp_eq]
      change dpBellman D ordered k S U a =
        maxWithZero ((legalActions D ordered S U).toList.map (dpBellman D ordered k S U))
      refine le_antisymm (le_maxWithZero_map _ _ ha_list) ?_
      exact maxWithZero_map_le _ _ (dpBellman_nonneg D ordered k S U ha) _
        (fun x hx => le_score_bestOf _ hbest x hx)

private def runPolicyExt {E : Type*} (π : OfflineStochMatching.UnitPatience.Policy E)
    (P : E → Bool) : ℕ → List (E × Bool) → List (E × Bool)
  | 0, h => h
  | k + 1, h =>
    match π (runPolicyExt π P k h) with
    | none => runPolicyExt π P k h
    | some e => runPolicyExt π P k h ++ [(e, P e)]

private lemma runPolicyExt_nil {E : Type*} (π : OfflineStochMatching.UnitPatience.Policy E)
    (P : E → Bool) :
    ∀ k : ℕ, runPolicyExt π P k [] = OfflineStochMatching.UnitPatience.runPolicy π P k
  | 0 => rfl
  | k + 1 => by
    change (match π (runPolicyExt π P k []) with
      | none => runPolicyExt π P k []
      | some e => runPolicyExt π P k [] ++ [(e, P e)]) =
      (match π (OfflineStochMatching.UnitPatience.runPolicy π P k) with
      | none => OfflineStochMatching.UnitPatience.runPolicy π P k
      | some e => OfflineStochMatching.UnitPatience.runPolicy π P k ++ [(e, P e)])
    rw [runPolicyExt_nil π P k]

private lemma runPolicyExt_shift {E : Type*} (π : OfflineStochMatching.UnitPatience.Policy E)
    (P : E → Bool) :
    ∀ (k : ℕ) (h : List (E × Bool)),
      runPolicyExt π P (k + 1) h =
        match π h with
        | none => h
        | some e => runPolicyExt π P k (h ++ [(e, P e)])
  | 0, _ => rfl
  | k + 1, h => by
    change (match π (runPolicyExt π P (k + 1) h) with
      | none => runPolicyExt π P (k + 1) h
      | some e => runPolicyExt π P (k + 1) h ++ [(e, P e)]) = _
    rw [runPolicyExt_shift π P k h]
    cases hπ : π h with
    | none => simp [hπ]
    | some e => rfl

private def histReward {n m : ℕ} (D : Instance n m) (h : History n m) : ℝ :=
  (h.map (fun z => if z.2 then actionReward D z.1 else 0)).sum

private lemma histReward_nil {n m : ℕ} (D : Instance n m) :
    histReward D [] = 0 := rfl

private lemma histReward_append_false {n m : ℕ} (D : Instance n m) (h : History n m)
    (a : Action n m) :
    histReward D (h ++ [(a, false)]) = histReward D h := by
  unfold histReward
  simp

private lemma histReward_append_true {n m : ℕ} (D : Instance n m) (h : History n m)
    (a : Action n m) :
    histReward D (h ++ [(a, true)]) = histReward D h + actionReward D a := by
  unfold histReward
  simp

private lemma legalize_some_iff {n m : ℕ} (D : Instance n m) (ordered : Bool)
    (π : DetPolicy n m) (h : History n m) (a : Action n m) :
    legalize D ordered π h = some a ↔
      π h = some a ∧ a ∈ legalActions D ordered (remainingResources h) (remainingArrivals h) := by
  unfold legalize
  cases π h with
  | none => simp
  | some b =>
    dsimp only
    split_ifs with hb
    · simp only [Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hb⟩
      · rintro ⟨rfl, _⟩; rfl
    · simp only [false_iff, not_and, Option.some.injEq]
      rintro rfl
      exact hb

private lemma runPolicyExt_update_of_not_mem {n m : ℕ} (D : Instance n m) (ordered : Bool)
    (π : DetPolicy n m) (ω : Outcome D) (e : Edge D) (b₀ : Bool) :
    ∀ (k : ℕ) (h : History n m), e.val.2 ∉ remainingArrivals h →
      runPolicyExt (legalize D ordered π) (actionBit D (Function.update ω e b₀)) k h =
        runPolicyExt (legalize D ordered π) (actionBit D ω) k h
  | 0, _, _ => rfl
  | k + 1, h, hnot => by
    rw [runPolicyExt_shift, runPolicyExt_shift]
    cases hleg : legalize D ordered π h with
    | none => rfl
    | some a =>
      dsimp only
      obtain ⟨_, ha⟩ := (legalize_some_iff D ordered π h a).mp hleg
      have ha1 : a.1 ∈ remainingArrivals h := by
        unfold legalActions at ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ha.1
      have hne_t : a.1 ≠ e.val.2 := fun heq => hnot (heq ▸ ha1)
      have hbit : actionBit D (Function.update ω e b₀) a = actionBit D ω a := by
        unfold actionBit
        cases ha2 : a.2 with
        | none => rfl
        | some i =>
          dsimp only
          unfold bit
          split_ifs with he'
          · have hne_edge : (⟨(i, a.1), he'⟩ : Edge D) ≠ e := by
              intro h_eq
              apply hne_t
              exact congrArg (fun x : Edge D => x.val.2) h_eq
            simp [hne_edge]
          · rfl
      rw [hbit]
      refine runPolicyExt_update_of_not_mem D ordered π ω e b₀ k
        (h ++ [(a, actionBit D ω a)]) ?_
      rw [remainingArrivals_append]
      exact fun hmem => hnot (Finset.mem_of_mem_erase hmem)

private lemma edgeAverage_runPolicyExt_eq {n m : ℕ} (D : Instance n m) (ordered : Bool)
    (π : DetPolicy n m) :
    ∀ (k : ℕ) (h : History n m),
      edgeAverage D (fun ω =>
        histReward D (runPolicyExt (legalize D ordered π) (actionBit D ω) k h)) =
        histReward D h + randomizedContinuation D ordered (pureRand π) k h
  | 0, h => by
    simp [runPolicyExt, randomizedContinuation, edgeAverage_const]
  | k + 1, h => by
    rw [randomizedContinuation_pureRand_succ]
    have hshift : (fun ω =>
        histReward D (runPolicyExt (legalize D ordered π) (actionBit D ω) (k + 1) h)) =
        (fun ω =>
          match legalize D ordered π h with
          | none => histReward D h
          | some a =>
            histReward D (runPolicyExt (legalize D ordered π) (actionBit D ω) k
              (h ++ [(a, actionBit D ω a)]))) := by
      funext ω
      rw [runPolicyExt_shift]
      cases legalize D ordered π h <;> rfl
    rw [hshift]
    cases hleg : legalize D ordered π h with
    | none =>
      simp [edgeAverage_const]
    | some a =>
      dsimp only
      obtain ⟨_, ha⟩ := (legalize_some_iff D ordered π h a).mp hleg
      cases ha2 : a.2 with
      | none =>
        have hbit : ∀ ω, actionBit D ω a = false := by
          intro ω; unfold actionBit; simp [ha2]
        have hprob : actionProbability D a = 0 := by
          unfold actionProbability; simp [ha2]
        simp_rw [hbit, hprob]
        rw [edgeAverage_runPolicyExt_eq D ordered π k (h ++ [(a, false)]),
          histReward_append_false]
        ring
      | some i =>
        have he : (i, a.1) ∈ D.edges := by
          unfold legalActions at ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, ha2] at ha
          exact ha.2.2.2
        let e : Edge D := ⟨(i, a.1), he⟩
        have hprob : actionProbability D a = D.probability e.val := by
          unfold actionProbability; simp [ha2, e]
        rw [← edgeAverage_resample D e]
        have hres : (fun ω => resample D e ω (fun w =>
            histReward D (runPolicyExt (legalize D ordered π) (actionBit D w) k
              (h ++ [(a, actionBit D w a)])))) =
            (fun ω =>
              (1 - D.probability e.val) *
                histReward D (runPolicyExt (legalize D ordered π) (actionBit D ω) k
                  (h ++ [(a, false)])) +
              D.probability e.val *
                histReward D (runPolicyExt (legalize D ordered π) (actionBit D ω) k
                  (h ++ [(a, true)]))) := by
          funext ω
          unfold resample
          dsimp only
          have hbit_f : actionBit D (Function.update ω e false) a = false := by
            unfold actionBit bit
            simp [ha2, he, e]
          have hbit_t : actionBit D (Function.update ω e true) a = true := by
            unfold actionBit bit
            simp [ha2, he, e]
          have hnot_f : e.val.2 ∉ remainingArrivals (h ++ [(a, false)]) := by
            rw [remainingArrivals_append]
            exact Finset.notMem_erase a.1 (remainingArrivals h)
          have hnot_t : e.val.2 ∉ remainingArrivals (h ++ [(a, true)]) := by
            rw [remainingArrivals_append]
            exact Finset.notMem_erase a.1 (remainingArrivals h)
          rw [hbit_f, hbit_t,
            runPolicyExt_update_of_not_mem D ordered π ω e false k _ hnot_f,
            runPolicyExt_update_of_not_mem D ordered π ω e true k _ hnot_t]
        rw [hres, edgeAverage_add, edgeAverage_const_mul, edgeAverage_const_mul,
          edgeAverage_runPolicyExt_eq D ordered π k (h ++ [(a, false)]),
          edgeAverage_runPolicyExt_eq D ordered π k (h ++ [(a, true)]),
          histReward_append_false, histReward_append_true, hprob]
        ring

private lemma deterministicValue_eq_randomizedValue_pureRand {n m : ℕ} (D : Instance n m)
    (ordered : Bool) (π : DetPolicy n m) :
    deterministicValue D ordered π = randomizedValue D ordered (pureRand π) := by
  unfold deterministicValue randomizedValue
  have h := edgeAverage_runPolicyExt_eq D ordered π m []
  rw [histReward_nil, zero_add] at h
  rw [← h]
  congr 1
  funext ω
  rw [runPolicyExt_nil]
  rfl

private lemma lemma_1_for_ordered {n m : ℕ} (D : Instance n m) (ordered : Bool) :
    deterministicValue D ordered (dpPolicy D ordered) = dp D ordered m Finset.univ Finset.univ ∧
      benchmark D ordered = deterministicValue D ordered (dpPolicy D ordered) := by
  have hdet : deterministicValue D ordered (dpPolicy D ordered) =
      dp D ordered m Finset.univ Finset.univ := by
    rw [deterministicValue_eq_randomizedValue_pureRand]
    unfold randomizedValue
    have h := randomizedContinuation_dpPolicy D ordered m []
      (by rw [remainingArrivals_nil, Finset.card_univ, Fintype.card_fin])
    simpa [remainingResources_nil, remainingArrivals_nil] using h
  refine ⟨hdet, ?_⟩
  unfold benchmark
  rw [hdet]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨randomizedValue D ordered (pureRand (dpPolicy D ordered)), ⟨_, rfl⟩⟩ ?_ ?_
  · rintro _ ⟨π, rfl⟩
    unfold randomizedValue
    have h := randomizedContinuation_le_dp D ordered π m []
    simpa [remainingResources_nil, remainingArrivals_nil] using h
  · intro w hw
    refine ⟨deterministicValue D ordered (dpPolicy D ordered), ?_, ?_⟩
    · rw [deterministicValue_eq_randomizedValue_pureRand]
      exact ⟨pureRand (dpPolicy D ordered), rfl⟩
    · linarith

theorem solution {n m : ℕ} (D : Instance n m) :
    (deterministicValue D true (dpPolicy D true) = dp D true m Finset.univ Finset.univ ∧
      benchmark D true = deterministicValue D true (dpPolicy D true)) ∧
    (deterministicValue D false (dpPolicy D false) = dp D false m Finset.univ Finset.univ ∧
      benchmark D false = deterministicValue D false (dpPolicy D false)) :=
  ⟨lemma_1_for_ordered D true, lemma_1_for_ordered D false⟩

end
