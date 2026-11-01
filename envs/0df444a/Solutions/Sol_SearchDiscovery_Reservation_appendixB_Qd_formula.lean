-- Prove2me | solution 1 for SearchDiscovery.Reservation.appendixB_Qd_formula
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:38:48.426254+00:00
-- url     : https://prove2.me/submissions/103dd453-6b76-4582-8d43-fa4987c81d41

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model
import Theorems.Thm_SearchDiscovery_Reservation_eq6_unique_solution

open SearchDiscovery.Reservation MeasureTheory ProbabilityTheory

namespace SDQd

variable (M : SDModel)

/-- A fixed realisation, used to run the deterministic dynamics once discovery is unavailable. -/
def ω₀ : M.Ω := (fun _ => 0, fun _ => (fun _ => (0, 0), true))

/-- One period with discovery unavailable (the randomness is then never read). -/
def dstep (π : InfoState → Act) (r : RunState) : RunState := M.step π (ω₀ M) r

lemma step_eq_dstep (π : InfoState → Act) (ω : M.Ω) (r : RunState) (h : r.disc = false) :
    M.step π ω r = dstep M π r := by
  unfold dstep SDModel.step
  rcases r.bought with _ | b
  · cases π r.info <;> simp [h]
  · rfl

lemma dstep_disc (π : InfoState → Act) (r : RunState) (h : r.disc = false) :
    (dstep M π r).disc = false := by
  unfold dstep SDModel.step
  rcases r.bought with _ | b
  · cases π r.info with
    | buy i => by_cases hi : i < r.C.length <;> simp [hi, h]
    | inspect i => by_cases hi : i < r.S.length <;> simp [hi, h]
    | discover => simp [h]
  · exact h

lemma run_eq_iter (π : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) (h : s₀.disc = false) :
    ∀ t, M.run π s₀ ω t = (dstep M π)^[t] (M.initRun s₀ ω) ∧
      ((dstep M π)^[t] (M.initRun s₀ ω)).disc = false := by
  intro t
  induction t with
  | zero => exact ⟨rfl, h⟩
  | succ t ih =>
    have e1 : M.run π s₀ ω (t + 1) = M.step π ω (M.run π s₀ ω t) := by
      simp only [SDModel.run]; rw [Function.iterate_succ_apply']
    rw [e1, ih.1, Function.iterate_succ_apply', step_eq_dstep M π ω _ ih.2]
    exact ⟨rfl, dstep_disc M π _ ih.2⟩

open Classical in
/-- The payoff of the deterministic run from a run state. -/
noncomputable def Φ (π : InfoState → Act) (r : RunState) : ℝ :=
  if h : ∃ t, ((dstep M π)^[t] r).bought.isSome then
    ((dstep M π)^[Nat.find h] r).bought.getD 0 - ((dstep M π)^[Nat.find h] r).cost
  else 0

/-- The run from `r` takes available actions until it buys, and it buys. -/
def Good (π : InfoState → Act) (r : RunState) : Prop :=
  (∀ t, ((dstep M π)^[t] r).bought = none →
      Available ((dstep M π)^[t] r).info (π ((dstep M π)^[t] r).info)) ∧
  ∃ t, ((dstep M π)^[t] r).bought.isSome

lemma payoff_eq_Φ (π : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) (h : s₀.disc = false) :
    M.payoff π s₀ ω = Φ M π (M.initRun s₀ ω) := by
  have hr : ∀ t, M.run π s₀ ω t = (dstep M π)^[t] (M.initRun s₀ ω) :=
    fun t => (run_eq_iter M π s₀ ω h t).1
  have hrun : M.run π s₀ ω = fun t => (dstep M π)^[t] (M.initRun s₀ ω) := funext hr
  unfold SDModel.payoff Φ
  rw [hrun]

lemma feasible_iff (π : InfoState → Act) (s₀ : InfoState) (h : s₀.disc = false) :
    M.Feasible π s₀ ↔ (∀ᵐ ω ∂M.P s₀, Good M π (M.initRun s₀ ω)) ∧
      Integrable (fun ω => Φ M π (M.initRun s₀ ω)) (M.P s₀) := by
  have hr : ∀ ω t, M.run π s₀ ω t = (dstep M π)^[t] (M.initRun s₀ ω) :=
    fun ω t => (run_eq_iter M π s₀ ω h t).1
  have hp : M.payoff π s₀ = fun ω => Φ M π (M.initRun s₀ ω) :=
    funext fun ω => payoff_eq_Φ M π s₀ ω h
  unfold SDModel.Feasible Good
  simp only [hr, hp]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1.and h2, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1.mono fun _ h => h.1, h1.mono fun _ h => h.2, h3⟩

lemma dstep_bought (π : InfoState → Act) (r : RunState) (b : ℝ) (h : r.bought = some b) :
    dstep M π r = r := by
  simp [dstep, SDModel.step, h]

lemma iter_bought (π : InfoState → Act) (r : RunState) (b : ℝ) (h : r.bought = some b) :
    ∀ t, (dstep M π)^[t] r = r := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, dstep_bought M π r b h]

lemma Φ_bought (π : InfoState → Act) (r : RunState) (b : ℝ) (h : r.bought = some b) :
    Φ M π r = b - r.cost := by
  classical
  have hex : ∃ t, ((dstep M π)^[t] r).bought.isSome := ⟨0, by simp [h]⟩
  have h0 : Nat.find hex = 0 := by simp [Nat.find_eq_zero, h]
  unfold Φ
  rw [dif_pos hex]
  simp only [h0, Function.iterate_zero, id, h, Option.getD_some]

lemma Good_bought (π : InfoState → Act) (r : RunState) (b : ℝ) (h : r.bought = some b) :
    Good M π r := by
  refine ⟨fun t ht => ?_, ⟨0, by simp [h]⟩⟩
  rw [iter_bought M π r b h t, h] at ht
  cases ht

lemma Φ_step (π : InfoState → Act) (r : RunState) (h : r.bought = none) :
    Φ M π r = Φ M π (dstep M π r) := by
  classical
  have hs : ∀ t, (dstep M π)^[t + 1] r = (dstep M π)^[t] (dstep M π r) :=
    fun t => Function.iterate_succ_apply _ _ _
  by_cases h2 : ∃ t, ((dstep M π)^[t] (dstep M π r)).bought.isSome
  · have h1 : ∃ t, ((dstep M π)^[t] r).bought.isSome := by
      obtain ⟨t, ht⟩ := h2; exact ⟨t + 1, by rw [hs]; exact ht⟩
    have h2' : ∃ t, ((dstep M π)^[t + 1] r).bought.isSome := by
      obtain ⟨t, ht⟩ := h2; exact ⟨t, by rw [hs]; exact ht⟩
    have hf : Nat.find h1 = Nat.find h2' + 1 :=
      Nat.find_comp_succ h1 h2' (by simp [h])
    have hf2 : Nat.find h2' = Nat.find h2 := by
      simp only [hs]
    unfold Φ
    rw [dif_pos h1, dif_pos h2, hf, hf2, hs]
  · have h1 : ¬ ∃ t, ((dstep M π)^[t] r).bought.isSome := by
      rintro ⟨t, ht⟩
      rcases t with _ | t
      · simp [h] at ht
      · exact h2 ⟨t, by rw [← hs]; exact ht⟩
    unfold Φ
    rw [dif_neg h1, dif_neg h2]

lemma Good_step (π : InfoState → Act) (r : RunState) (h : r.bought = none) :
    Good M π r ↔ Available r.info (π r.info) ∧ Good M π (dstep M π r) := by
  have hs : ∀ t, (dstep M π)^[t + 1] r = (dstep M π)^[t] (dstep M π r) :=
    fun t => Function.iterate_succ_apply _ _ _
  constructor
  · rintro ⟨h1, t, ht⟩
    refine ⟨h1 0 h, fun t ht => ?_, ?_⟩
    · rw [← hs] at ht ⊢; exact h1 _ ht
    · rcases t with _ | t
      · simp [h] at ht
      · exact ⟨t, by rw [← hs]; exact ht⟩
  · rintro ⟨ha, h1, t, ht⟩
    refine ⟨fun t ht => ?_, ⟨t + 1, by rw [hs]; exact ht⟩⟩
    rcases t with _ | t
    · exact ha
    · rw [hs] at ht ⊢; exact h1 t ht

/-- The run state with consideration set `C`, awareness products with partial valuations `xs`
and hidden values `ys`, no discovery, and costs `c` paid so far. -/
def st {n : ℕ} (C : List ℝ) (xs ys : Fin n → ℝ) (c : ℝ) : RunState :=
  ⟨C, List.ofFn (fun k => (xs k, ys k)), false, 0, c, none⟩

lemma st_info {n : ℕ} (C : List ℝ) (xs ys : Fin n → ℝ) (c : ℝ) :
    (st C xs ys c).info = ⟨C, List.ofFn xs, false⟩ := by
  simp [st, RunState.info, List.map_ofFn, Function.comp_def]

lemma ofFn_eraseIdx {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) (i : Fin (n + 1)) :
    (List.ofFn f).eraseIdx i = List.ofFn (f ∘ i.succAbove) := by
  apply List.ext_getElem
  · have := i.is_lt
    simp [List.length_eraseIdx]; omega
  · intro j h1 h2
    simp only [List.getElem_ofFn, Function.comp_apply]
    rw [List.getElem_eraseIdx]
    simp only [List.getElem_ofFn]
    congr 1
    simp only [List.length_ofFn] at h2
    split_ifs with hj
    · rw [Fin.succAbove_of_castSucc_lt]; · rfl
      · simp [Fin.lt_def]; omega
    · rw [Fin.succAbove_of_le_castSucc]; · rfl
      · simp [Fin.le_def]; omega

lemma dstep_st_buy {n : ℕ} (π : InfoState → Act) (C : List ℝ) (xs ys : Fin n → ℝ) (c : ℝ)
    (j : ℕ) (hπ : π ⟨C, List.ofFn xs, false⟩ = .buy j) (hj : j < C.length) :
    Φ M π (st C xs ys c) = C[j] - c ∧ Good M π (st C xs ys c) := by
  have hd : dstep M π (st C xs ys c) = { st C xs ys c with bought := some C[j] } := by
    have hb : (st C xs ys c).bought = none := rfl
    unfold dstep
    simp only [SDModel.step, hb, st_info, hπ]
    rw [dif_pos (show j < (st C xs ys c).C.length from hj)]
    rfl
  have hb2 : (dstep M π (st C xs ys c)).bought = some C[j] := by rw [hd]
  refine ⟨?_, ?_⟩
  · rw [Φ_step M π _ rfl, Φ_bought M π _ _ hb2, hd]; rfl
  · rw [Good_step M π _ rfl, st_info, hπ]
    exact ⟨hj, Good_bought M π _ _ hb2⟩

lemma dstep_st_inspect {n : ℕ} (π : InfoState → Act) (C : List ℝ) (xs ys : Fin (n + 1) → ℝ)
    (c : ℝ) (i : Fin (n + 1)) (hπ : π ⟨C, List.ofFn xs, false⟩ = .inspect i) :
    dstep M π (st C xs ys c) =
      st (C ++ [xs i + ys i]) (xs ∘ i.succAbove) (ys ∘ i.succAbove) (c + M.cs) := by
  have hb : (st C xs ys c).bought = none := rfl
  unfold dstep
  simp only [SDModel.step, hb, st_info, hπ]
  have := i.is_lt
  rw [dif_pos (show (i : ℕ) < (st C xs ys c).S.length by simp [st]; omega)]
  simp only [st, List.getElem_ofFn, Fin.eta]
  rw [ofFn_eraseIdx (fun k => (xs k, ys k)) i]
  rfl

end SDQd

namespace SDQd

/-- `max {m, g 0, …, g (n-1)}`. -/
noncomputable def Wg {n : ℕ} (m : ℝ) (g : Fin n → ℝ) : ℝ := Finset.univ.fold max m g

lemma Wg_le_iff {n : ℕ} (m c : ℝ) (g : Fin n → ℝ) : Wg m g ≤ c ↔ m ≤ c ∧ ∀ k, g k ≤ c := by
  simp [Wg, Finset.fold_max_le]

lemma le_Wg {n : ℕ} (m : ℝ) (g : Fin n → ℝ) : m ≤ Wg m g := ((Wg_le_iff m _ g).mp le_rfl).1

lemma g_le_Wg {n : ℕ} (m : ℝ) (g : Fin n → ℝ) (k : Fin n) : g k ≤ Wg m g :=
  ((Wg_le_iff m _ g).mp le_rfl).2 k

lemma eq_of_le_iff {a b : ℝ} (h : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
  le_antisymm ((h b).mpr le_rfl) ((h a).mp le_rfl)

lemma Wg_succAbove {n : ℕ} (m : ℝ) (g : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Wg m g = max (g i) (Wg m (g ∘ i.succAbove)) := by
  refine eq_of_le_iff fun c => ?_
  rw [Wg_le_iff, max_le_iff, Wg_le_iff, Fin.forall_iff_succAbove i]
  simp only [Function.comp_apply]
  tauto

lemma Wg_max {n : ℕ} (m v : ℝ) (g : Fin n → ℝ) : Wg (max m v) g = max v (Wg m g) := by
  refine eq_of_le_iff fun c => ?_
  rw [Wg_le_iff, max_le_iff, max_le_iff, Wg_le_iff]
  tauto

lemma Wg_measurable {α : Type*} [MeasurableSpace α] {n : ℕ} (m : α → ℝ) (g : Fin n → α → ℝ)
    (hm : Measurable m) (hg : ∀ k, Measurable (g k)) :
    Measurable fun a => Wg (m a) (fun k => g k a) := by
  refine measurable_of_Iic fun c => ?_
  have : (fun a => Wg (m a) (fun k => g k a)) ⁻¹' Set.Iic c =
      {a | m a ≤ c} ∩ ⋂ k, {a | g k a ≤ c} := by
    ext a; simp [Wg_le_iff]
  rw [this]
  exact (measurableSet_le hm measurable_const).inter
    (MeasurableSet.iInter fun k => measurableSet_le (hg k) measurable_const)

lemma abs_Wg_le {n : ℕ} (m : ℝ) (g v : Fin n → ℝ) (hgv : ∀ k, g k ≤ v k) :
    |Wg m g| ≤ |m| + ∑ k, |v k| := by
  have hs : 0 ≤ ∑ k, |v k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  rw [abs_le]
  constructor
  · have := le_Wg m g
    have := neg_abs_le m
    linarith
  · rw [Wg_le_iff]
    refine ⟨by linarith [le_abs_self m], fun k => ?_⟩
    have h1 : |v k| ≤ ∑ k, |v k| :=
      Finset.single_le_sum (f := fun k => |v k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)
    linarith [hgv k, le_abs_self (v k), abs_nonneg m]

variable (M : SDModel)

/-- The bound `max {m, min(z^s(x_k), x_k + y_k)}`. -/
noncomputable def W (zs : ℝ → ℝ) {n : ℕ} (m : ℝ) (xs ys : Fin n → ℝ) : ℝ :=
  Wg m (fun k => min (zs (xs k)) (xs k + ys k))

/-- The law of the hidden values of products with partial valuations `xs`. -/
noncomputable def ν {n : ℕ} (xs : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun k => M.κ (xs k)

instance {n : ℕ} (xs : Fin n → ℝ) : IsProbabilityMeasure (ν M xs) := by
  unfold ν; infer_instance

lemma integrable_y (hM : M.Standing) (x : ℝ) : Integrable (fun y : ℝ => y) (M.κ x) :=
  (hM.memLp_κ x).integrable (by norm_num)

lemma integrable_coord (hM : M.Standing) {n : ℕ} (xs : Fin n → ℝ) (k : Fin n) :
    Integrable (fun ys : Fin n → ℝ => xs k + ys k) (ν M xs) := by
  have hmp : MeasurePreserving (Function.eval k) (ν M xs) (M.κ (xs k)) :=
    measurePreserving_eval _ k
  exact hmp.integrable_comp_of_integrable ((integrable_const (xs k)).add (integrable_y M hM _))

lemma W_measurable (zs : ℝ → ℝ) {n : ℕ} (xs : Fin n → ℝ) :
    Measurable fun p : ℝ × (Fin n → ℝ) => W zs p.1 xs p.2 := by
  unfold W
  exact Wg_measurable (fun p : ℝ × (Fin n → ℝ) => p.1)
    (fun k p => min (zs (xs k)) (xs k + p.2 k)) measurable_fst
    (fun k => measurable_const.min (measurable_const.add
      ((measurable_pi_apply k).comp measurable_snd)))

lemma W_measurable' (zs : ℝ → ℝ) {n : ℕ} (m : ℝ) (xs : Fin n → ℝ) :
    Measurable fun ys : Fin n → ℝ => W zs m xs ys :=
  (W_measurable zs xs).comp (measurable_const.prodMk measurable_id)

lemma abs_W_le (zs : ℝ → ℝ) {n : ℕ} (m : ℝ) (xs ys : Fin n → ℝ) :
    |W zs m xs ys| ≤ |m| + ∑ k, |xs k + ys k| :=
  abs_Wg_le m _ _ fun k => min_le_right _ _

lemma integrable_W (hM : M.Standing) (zs : ℝ → ℝ) {n : ℕ} (m : ℝ) (xs : Fin n → ℝ) :
    Integrable (fun ys => W zs m xs ys) (ν M xs) := by
  refine Integrable.mono' ((integrable_const |m|).add
    (integrable_finset_sum Finset.univ fun k _ => (integrable_coord M hM xs k).abs))
    (W_measurable' zs m xs).aestronglyMeasurable (Filter.Eventually.of_forall fun ys => ?_)
  rw [Real.norm_eq_abs]
  simpa using abs_W_le zs m xs ys

lemma integrable_excess (hM : M.Standing) (x z : ℝ) :
    Integrable (fun y : ℝ => max 0 (x + y - z)) (M.κ x) :=
  (integrable_const (0:ℝ)).sup (((integrable_const x).add (integrable_y M hM x)).sub
    (integrable_const z))

lemma excess_eq (zs : ℝ → ℝ) (hzs : ∀ x, M.Qs x (zs x) = 0) (x : ℝ) :
    ∫ y, max 0 (x + y - zs x) ∂M.κ x = M.cs := by
  have := hzs x
  unfold SDModel.Qs at this
  linarith

/-- The pointwise amortisation inequality. -/
lemma key_ineq (v z R : ℝ) : max v R ≤ max (min z v) R + max 0 (v - z) := by
  rcases le_total v z with h | h
  · rw [min_eq_right h]; linarith [le_max_left 0 (v - z)]
  · rw [min_eq_left h]
    rcases le_total v R with h2 | h2
    · rw [max_eq_right h2, max_eq_right (h.trans h2)]; linarith [le_max_left 0 (v - z)]
    · rw [max_eq_left h2]
      have := le_max_right 0 (v - z)
      have := le_max_left z R
      linarith

lemma key_eq (v z R : ℝ) (hR : R ≤ z) : max v R = max (min z v) R + max 0 (v - z) := by
  rcases le_total v z with h | h
  · rw [min_eq_right h, max_eq_left (by linarith : v - z ≤ 0)]; ring
  · rw [min_eq_left h, max_eq_right (by linarith : (0:ℝ) ≤ v - z), max_eq_left (h.trans' hR),
      max_eq_left hR]
    ring

end SDQd

namespace SDQd

variable (M : SDModel)

lemma split_mp {n : ℕ} (xs : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i) (ν M xs)
      ((M.κ (xs i)).prod (ν M (xs ∘ i.succAbove))) :=
  measurePreserving_piFinSuccAbove (fun k => M.κ (xs k)) i

lemma split_apply {n : ℕ} (i : Fin (n + 1)) (ys : Fin (n + 1) → ℝ) :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i ys = (ys i, ys ∘ i.succAbove) :=
  rfl

lemma W_split (zs : ℝ → ℝ) {n : ℕ} (m : ℝ) (xs ys : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    W zs m xs ys = max (min (zs (xs i)) (xs i + ys i)) (W zs m (xs ∘ i.succAbove) (ys ∘ i.succAbove)) :=
  Wg_succAbove m _ i

lemma W_max (zs : ℝ → ℝ) {n : ℕ} (m v : ℝ) (xs ys : Fin n → ℝ) :
    W zs (max m v) xs ys = max v (W zs m xs ys) := Wg_max m v _

lemma buy_case (hM : M.Standing) (zs : ℝ → ℝ) {n : ℕ} (xs : Fin n → ℝ) (C : List ℝ) (m c : ℝ)
    (π : InfoState → Act) (hC : ∀ a ∈ C, a ≤ m) (j : ℕ)
    (hπ : π ⟨C, List.ofFn xs, false⟩ = .buy j) (hj : j < C.length) :
    ∫ ys, Φ M π (st C xs ys c) ∂ν M xs ≤ ∫ ys, W zs m xs ys ∂ν M xs - c := by
  have h1 : (fun ys => Φ M π (st C xs ys c)) = fun _ => C[j] - c :=
    funext fun ys => (dstep_st_buy M π C xs ys c j hπ hj).1
  rw [h1]
  have h2 : ∫ _ : Fin n → ℝ, m ∂ν M xs ≤ ∫ ys, W zs m xs ys ∂ν M xs :=
    integral_mono (integrable_const _) (integrable_W M hM zs m xs) fun ys => le_Wg _ _
  simp only [integral_const, probReal_univ, one_smul] at h2 ⊢
  have := hC _ (List.getElem_mem hj)
  linarith

theorem upper (hM : M.Standing) (zs : ℝ → ℝ) (hzs : ∀ x, M.Qs x (zs x) = 0) :
    ∀ (n : ℕ) (xs : Fin n → ℝ) (C : List ℝ) (m c : ℝ) (π : InfoState → Act),
      (∀ a ∈ C, a ≤ m) → (∀ᵐ ys ∂ν M xs, Good M π (st C xs ys c)) →
      Integrable (fun ys => Φ M π (st C xs ys c)) (ν M xs) →
      ∫ ys, Φ M π (st C xs ys c) ∂ν M xs ≤ ∫ ys, W zs m xs ys ∂ν M xs - c := by
  intro n
  induction n with
  | zero =>
    intro xs C m c π hC hG hI
    obtain ⟨ys0, hys0⟩ := hG.exists
    have ha := ((Good_step M π _ rfl).mp hys0).1
    rw [st_info] at ha
    cases hπ : π ⟨C, List.ofFn xs, false⟩ with
    | buy j =>
      rw [hπ] at ha
      exact buy_case M hM zs xs C m c π hC j hπ ha
    | inspect i => rw [hπ] at ha; exact absurd ha (by simp [Available])
    | discover => rw [hπ] at ha; exact absurd ha (by simp [Available])
  | succ n ih =>
    intro xs C m c π hC hG hI
    obtain ⟨ys0, hys0⟩ := hG.exists
    have ha := ((Good_step M π _ rfl).mp hys0).1
    rw [st_info] at ha
    cases hπ : π ⟨C, List.ofFn xs, false⟩ with
    | buy j =>
      rw [hπ] at ha
      exact buy_case M hM zs xs C m c π hC j hπ ha
    | discover => rw [hπ] at ha; exact absurd ha (by simp [Available])
    | inspect i0 =>
      rw [hπ] at ha
      have hi0 : i0 < n + 1 := by simpa [Available] using ha
      set i : Fin (n + 1) := ⟨i0, hi0⟩ with hi
      have hπ' : π ⟨C, List.ofFn xs, false⟩ = .inspect i := hπ
      set xs' := xs ∘ i.succAbove with hxs'
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
      have hmp : MeasurePreserving e (ν M xs) ((M.κ (xs i)).prod (ν M xs')) := split_mp M xs i
      set F : ℝ × (Fin n → ℝ) → ℝ :=
        fun q => Φ M π (st (C ++ [xs i + q.1]) xs' q.2 (c + M.cs)) with hF
      have hFe : ∀ ys, Φ M π (st C xs ys c) = F (e ys) := by
        intro ys
        rw [Φ_step M π _ rfl, dstep_st_inspect M π C xs ys c i hπ']
        rfl
      have hFe' : (fun ys => Φ M π (st C xs ys c)) = F ∘ e := funext hFe
      have hFint : Integrable F ((M.κ (xs i)).prod (ν M xs')) := by
        rw [← hmp.integrable_comp_emb e.measurableEmbedding, ← hFe']; exact hI
      have hFgood : ∀ᵐ q ∂(M.κ (xs i)).prod (ν M xs'),
          Good M π (st (C ++ [xs i + q.1]) xs' q.2 (c + M.cs)) := by
        rw [← hmp.map_eq, e.measurableEmbedding.ae_map_iff]
        filter_upwards [hG] with ys hys
        have := ((Good_step M π _ rfl).mp hys).2
        rwa [dstep_st_inspect M π C xs ys c i hπ'] at this
      -- the bound function after inspection
      set H : ℝ × (Fin n → ℝ) → ℝ := fun q => max (xs i + q.1) (W zs m xs' q.2) with hH
      set K : ℝ × (Fin n → ℝ) → ℝ :=
        fun q => max (min (zs (xs i)) (xs i + q.1)) (W zs m xs' q.2) with hK
      have hWm := W_measurable' zs m xs'
      have hHm : Measurable H :=
        (measurable_const.add measurable_fst).max (hWm.comp measurable_snd)
      have hKm : Measurable K :=
        (measurable_const.min (measurable_const.add measurable_fst)).max (hWm.comp measurable_snd)
      have hv : Integrable (fun q : ℝ × (Fin n → ℝ) => |xs i + q.1| + |W zs m xs' q.2|)
          ((M.κ (xs i)).prod (ν M xs')) :=
        (((integrable_const (xs i)).add (integrable_y M hM _)).abs.comp_fst _).add
          ((integrable_W M hM zs m xs').abs.comp_snd _)
      have hHint : Integrable H ((M.κ (xs i)).prod (ν M xs')) := by
        refine Integrable.mono' hv hHm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun q => ?_)
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have := le_max_right (xs i + q.1) (W zs m xs' q.2)
          have := neg_abs_le (W zs m xs' q.2)
          have := abs_nonneg (xs i + q.1)
          linarith
        · refine max_le ?_ ?_
          · linarith [le_abs_self (xs i + q.1), abs_nonneg (W zs m xs' q.2)]
          · linarith [le_abs_self (W zs m xs' q.2), abs_nonneg (xs i + q.1)]
      have hKint : Integrable K ((M.κ (xs i)).prod (ν M xs')) := by
        refine Integrable.mono' hv hKm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun q => ?_)
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have := le_max_right (min (zs (xs i)) (xs i + q.1)) (W zs m xs' q.2)
          have := neg_abs_le (W zs m xs' q.2)
          have := abs_nonneg (xs i + q.1)
          linarith
        · refine max_le ?_ ?_
          · linarith [min_le_right (zs (xs i)) (xs i + q.1), le_abs_self (xs i + q.1),
              abs_nonneg (W zs m xs' q.2)]
          · linarith [le_abs_self (W zs m xs' q.2), abs_nonneg (xs i + q.1)]
      -- step 1: the induction hypothesis on almost every section
      have hsec : ∀ᵐ y ∂M.κ (xs i), ∫ ys', F (y, ys') ∂ν M xs' ≤
          (∫ ys', H (y, ys') ∂ν M xs') - (c + M.cs) := by
        filter_upwards [hFint.prod_right_ae, Measure.ae_ae_of_ae_prod hFgood] with y hy1 hy2
        have := ih xs' (C ++ [xs i + y]) (max m (xs i + y)) (c + M.cs) π
          (by
            intro a ha
            rcases List.mem_append.mp ha with h | h
            · exact (hC a h).trans (le_max_left _ _)
            · rw [List.mem_singleton.mp h]; exact le_max_right _ _)
          hy2 hy1
        simpa only [hH, W_max] using this
      have step1 : ∫ ys, Φ M π (st C xs ys c) ∂ν M xs ≤
          (∫ q, H q ∂(M.κ (xs i)).prod (ν M xs')) - (c + M.cs) := by
        rw [hFe', show (∫ ys, (F ∘ e) ys ∂ν M xs) = ∫ ys, F (e ys) ∂ν M xs from rfl,
          hmp.integral_comp' F, integral_prod F hFint, integral_prod H hHint]
        have hI2 : Integrable (fun y => (∫ ys', H (y, ys') ∂ν M xs') - (c + M.cs))
            (M.κ (xs i)) := hHint.integral_prod_left.sub (integrable_const _)
        have := integral_mono_ae hFint.integral_prod_left hI2 hsec
        rw [integral_sub hHint.integral_prod_left (integrable_const _)] at this
        simpa using this
      -- step 2: the amortisation inequality in the inspected coordinate
      have hsec2 : ∀ ys' : Fin n → ℝ, ∫ y, H (y, ys') ∂M.κ (xs i) ≤
          (∫ y, K (y, ys') ∂M.κ (xs i)) + M.cs := by
        intro ys'
        have hHy : Integrable (fun y => H (y, ys')) (M.κ (xs i)) := by
          show Integrable (fun y => max (xs i + y) (W zs m xs' ys')) _
          exact ((integrable_const (xs i)).add (integrable_y M hM _)).sup (integrable_const _)
        have hKy : Integrable (fun y => K (y, ys')) (M.κ (xs i)) := by
          show Integrable (fun y => max (min (zs (xs i)) (xs i + y)) (W zs m xs' ys')) _
          exact ((integrable_const _).inf ((integrable_const (xs i)).add
            (integrable_y M hM _))).sup (integrable_const _)
        have hI4 : Integrable (fun y => K (y, ys') + max 0 (xs i + y - zs (xs i))) (M.κ (xs i)) :=
          hKy.add (integrable_excess M hM (xs i) (zs (xs i)))
        have := integral_mono hHy hI4
          (fun y => key_ineq (xs i + y) (zs (xs i)) (W zs m xs' ys'))
        rw [integral_add hKy (integrable_excess M hM _ _), excess_eq M zs hzs] at this
        exact this
      have step2 : ∫ q, H q ∂(M.κ (xs i)).prod (ν M xs') ≤
          (∫ q, K q ∂(M.κ (xs i)).prod (ν M xs')) + M.cs := by
        rw [integral_prod_symm H hHint, integral_prod_symm K hKint]
        have hI3 : Integrable (fun ys' => (∫ y, K (y, ys') ∂M.κ (xs i)) + M.cs) (ν M xs') :=
          hKint.integral_prod_right.add (integrable_const M.cs)
        have := integral_mono hHint.integral_prod_right hI3 hsec2
        rw [integral_add hKint.integral_prod_right (integrable_const _)] at this
        simpa using this
      -- step 3: back to the original coordinates
      have step3 : ∫ q, K q ∂(M.κ (xs i)).prod (ν M xs') = ∫ ys, W zs m xs ys ∂ν M xs := by
        rw [← hmp.integral_comp' K]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ys => ?_)
        simp only [hK, split_apply, he]
        rw [W_split zs m xs ys i]
      linarith

end SDQd

namespace SDQd

open Classical in
/-- The position of a largest entry of a list (the first one, scanning from the back). -/
noncomputable def bestIdx : List ℝ → ℕ
  | [] => 0
  | a :: l => if ∀ b ∈ l, b ≤ a then 0 else bestIdx l + 1

lemma bestIdx_spec : ∀ L : List ℝ, L ≠ [] →
    bestIdx L < L.length ∧ ∀ b ∈ L, b ≤ L.getD (bestIdx L) 0
  | [], h => absurd rfl h
  | a :: l, _ => by
    by_cases ha : ∀ b ∈ l, b ≤ a
    · have : bestIdx (a :: l) = 0 := by simp only [bestIdx]; rw [if_pos ha]
      rw [this]
      refine ⟨by simp, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with h | h
      · simp [h]
      · simpa using ha b h
    · have : bestIdx (a :: l) = bestIdx l + 1 := by simp only [bestIdx]; rw [if_neg ha]
      rw [this]
      have hl : l ≠ [] := by rintro rfl; exact ha (by simp)
      obtain ⟨h1, h2⟩ := bestIdx_spec l hl
      refine ⟨by simpa using h1, fun b hb => ?_⟩
      simp only [List.getD_cons_succ]
      rcases List.mem_cons.mp hb with h | h
      · push Not at ha
        obtain ⟨b', hb', hlt⟩ := ha
        rw [h]; exact hlt.le.trans (h2 b' hb')
      · exact h2 b h

lemma bestIdx_mem (L : List ℝ) (h : L ≠ []) : L.getD (bestIdx L) 0 ∈ L := by
  rw [List.getD_eq_getElem _ _ (bestIdx_spec L h).1]
  exact List.getElem_mem _

lemma best_append (C : List ℝ) (hC : C ≠ []) (v : ℝ) :
    (C ++ [v]).getD (bestIdx (C ++ [v])) 0 = max (C.getD (bestIdx C) 0) v := by
  have hC' : C ++ [v] ≠ [] := by simp
  obtain ⟨-, h1⟩ := bestIdx_spec _ hC'
  obtain ⟨-, h2⟩ := bestIdx_spec _ hC
  have m1 := bestIdx_mem _ hC'
  have m2 := bestIdx_mem _ hC
  apply le_antisymm
  · rcases List.mem_append.mp m1 with h | h
    · exact (h2 _ h).trans (le_max_left _ _)
    · rw [List.mem_singleton.mp h]; exact le_max_right _ _
  · exact max_le (h1 _ (List.mem_append_left _ m2)) (h1 _ (by simp))

/-- A largest coordinate of a tuple. -/
noncomputable def bestFin {n : ℕ} (f : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  ⟨bestIdx (List.ofFn f), by simpa using (bestIdx_spec (List.ofFn f) (by simp)).1⟩

lemma bestFin_spec {n : ℕ} (f : Fin (n + 1) → ℝ) (k : Fin (n + 1)) : f k ≤ f (bestFin f) := by
  have h := (bestIdx_spec (List.ofFn f) (by simp)).2 (f k) ((List.mem_ofFn ..).2 ⟨k, rfl⟩)
  rw [List.getD_eq_getElem _ _ (by simpa using (bestIdx_spec (List.ofFn f) (by simp)).1),
    List.getElem_ofFn] at h
  exact h

open Classical in
/-- The reservation-value policy without discovery: inspect a product with the largest search
value if it exceeds the best purchase value, otherwise buy a best product. -/
noncomputable def pistar (zs : ℝ → ℝ) (s : InfoState) : Act :=
  if s.S ≠ [] ∧ s.C.getD (bestIdx s.C) 0 < zs (s.S.getD (bestIdx (s.S.map zs)) 0) then
    .inspect (bestIdx (s.S.map zs))
  else .buy (bestIdx s.C)

lemma pistar_st0 (zs : ℝ → ℝ) (xs : Fin 0 → ℝ) (C : List ℝ) :
    pistar zs ⟨C, List.ofFn xs, false⟩ = .buy (bestIdx C) := by
  simp [pistar]

lemma pistar_st (zs : ℝ → ℝ) {n : ℕ} (xs : Fin (n + 1) → ℝ) (C : List ℝ) :
    pistar zs ⟨C, List.ofFn xs, false⟩ =
      if C.getD (bestIdx C) 0 < zs (xs (bestFin (zs ∘ xs))) then
        .inspect (bestFin (zs ∘ xs)) else .buy (bestIdx C) := by
  have h1 : (List.ofFn xs).map zs = List.ofFn (zs ∘ xs) := List.map_ofFn
  have h2 : (List.ofFn xs).getD (bestIdx (List.ofFn (zs ∘ xs))) 0 = xs (bestFin (zs ∘ xs)) := by
    have hb : bestIdx (List.ofFn (zs ∘ xs)) < (List.ofFn xs).length := by
      rw [List.length_ofFn]; exact (bestFin (zs ∘ xs)).2
    rw [List.getD_eq_getElem _ _ hb, List.getElem_ofFn]
    rfl
  have hne : List.ofFn xs ≠ [] := by simp
  unfold pistar
  simp only [h1, h2, ne_eq, hne, not_false_eq_true, true_and]
  rfl

/-- The realised payoff of `pistar` (plus the costs paid before), as a function of the best
purchase value `m` so far. -/
noncomputable def Hf (cs : ℝ) (zs : ℝ → ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ → (Fin n → ℝ) → ℝ
  | 0, _, m, _ => m
  | n + 1, xs, m, ys =>
    if m < zs (xs (bestFin (zs ∘ xs))) then
      Hf cs zs n (xs ∘ (bestFin (zs ∘ xs)).succAbove) (max m (xs (bestFin (zs ∘ xs)) +
        ys (bestFin (zs ∘ xs)))) (ys ∘ (bestFin (zs ∘ xs)).succAbove) - cs
    else m

variable (M : SDModel)

theorem pistar_run (zs : ℝ → ℝ) : ∀ (n : ℕ) (xs ys : Fin n → ℝ) (C : List ℝ) (c : ℝ), C ≠ [] →
    Good M (pistar zs) (st C xs ys c) ∧
      Φ M (pistar zs) (st C xs ys c) = Hf M.cs zs n xs (C.getD (bestIdx C) 0) ys - c := by
  intro n
  induction n with
  | zero =>
    intro xs ys C c hC
    have hj := (bestIdx_spec C hC).1
    obtain ⟨h1, h2⟩ := dstep_st_buy M (pistar zs) C xs ys c _ (pistar_st0 zs xs C) hj
    refine ⟨h2, ?_⟩
    rw [h1, List.getD_eq_getElem _ _ hj]
    rfl
  | succ n ih =>
    intro xs ys C c hC
    set i := bestFin (zs ∘ xs) with hi
    by_cases hm : C.getD (bestIdx C) 0 < zs (xs i)
    · have hπ : pistar zs ⟨C, List.ofFn xs, false⟩ = .inspect i := by
        rw [pistar_st, if_pos hm]
      have hd := dstep_st_inspect M (pistar zs) C xs ys c i hπ
      have hC' : C ++ [xs i + ys i] ≠ [] := by simp
      obtain ⟨g1, g2⟩ := ih (xs ∘ i.succAbove) (ys ∘ i.succAbove) _ (c + M.cs) hC'
      refine ⟨?_, ?_⟩
      · rw [Good_step M _ _ rfl, st_info, hπ, hd]
        exact ⟨by have := i.2; simp [Available]; omega, g1⟩
      · rw [Φ_step M _ _ rfl, hd, g2, best_append C hC]
        simp only [Hf, ← hi, if_pos hm]
        ring
    · have hπ : pistar zs ⟨C, List.ofFn xs, false⟩ = .buy (bestIdx C) := by
        rw [pistar_st, if_neg hm]
      have hj := (bestIdx_spec C hC).1
      obtain ⟨h1, h2⟩ := dstep_st_buy M (pistar zs) C xs ys c _ hπ hj
      refine ⟨h2, ?_⟩
      rw [h1, List.getD_eq_getElem _ _ hj]
      simp only [Hf, ← hi, if_neg (show ¬ C[bestIdx C] < zs (xs i) by
        rwa [List.getD_eq_getElem _ _ hj] at hm)]

lemma Hf_measurable (cs : ℝ) (zs : ℝ → ℝ) : ∀ (n : ℕ) (xs : Fin n → ℝ),
    Measurable fun p : ℝ × (Fin n → ℝ) => Hf cs zs n xs p.1 p.2 := by
  intro n
  induction n with
  | zero => intro xs; exact measurable_fst
  | succ n ih =>
    intro xs
    set i := bestFin (zs ∘ xs)
    have hg : Measurable fun p : ℝ × (Fin (n + 1) → ℝ) =>
        (max p.1 (xs i + p.2 i), p.2 ∘ i.succAbove) :=
      (measurable_fst.max (measurable_const.add ((measurable_pi_apply i).comp measurable_snd))).prodMk
        (measurable_pi_iff.mpr fun j => (measurable_pi_apply _).comp measurable_snd)
    have : (fun p : ℝ × (Fin (n + 1) → ℝ) => Hf cs zs (n + 1) xs p.1 p.2) =
        fun p => if p.1 < zs (xs i) then
          Hf cs zs n (xs ∘ i.succAbove) (max p.1 (xs i + p.2 i)) (p.2 ∘ i.succAbove) - cs
        else p.1 := by
      funext p; simp only [Hf]; rfl
    rw [this]
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      (((ih _).comp hg).sub_const _) measurable_fst

lemma Hf_bounds (cs : ℝ) (hcs : 0 ≤ cs) (zs : ℝ → ℝ) : ∀ (n : ℕ) (xs : Fin n → ℝ) (m : ℝ)
    (ys : Fin n → ℝ), m - n * cs ≤ Hf cs zs n xs m ys ∧
      Hf cs zs n xs m ys ≤ |m| + ∑ k, |xs k + ys k| := by
  intro n
  induction n with
  | zero => intro xs m ys; simp [Hf, le_abs_self]
  | succ n ih =>
    intro xs m ys
    set i := bestFin (zs ∘ xs) with hi
    have hs : ∑ k, |xs k + ys k| = |xs i + ys i| + ∑ k : Fin n, |xs (i.succAbove k) + ys (i.succAbove k)| :=
      Fin.sum_univ_succAbove (fun k => |xs k + ys k|) i
    have hs0 : 0 ≤ ∑ k : Fin n, |xs (i.succAbove k) + ys (i.succAbove k)| :=
      Finset.sum_nonneg fun k _ => abs_nonneg _
    by_cases hm : m < zs (xs i)
    · have e : Hf cs zs (n + 1) xs m ys = Hf cs zs n (xs ∘ i.succAbove) (max m (xs i + ys i))
          (ys ∘ i.succAbove) - cs := by simp only [Hf, ← hi, if_pos hm]
      rw [e]
      obtain ⟨h1, h2⟩ := ih (xs ∘ i.succAbove) (max m (xs i + ys i)) (ys ∘ i.succAbove)
      simp only [Function.comp_apply] at h2
      have h3 : |max m (xs i + ys i)| ≤ |m| + |xs i + ys i| := by
        rw [abs_le]; constructor
        · linarith [neg_abs_le m, le_max_left m (xs i + ys i), abs_nonneg (xs i + ys i)]
        · exact max_le (by linarith [le_abs_self m, abs_nonneg (xs i + ys i)])
            (by linarith [le_abs_self (xs i + ys i), abs_nonneg m])
      constructor
      · push_cast
        linarith [le_max_left m (xs i + ys i)]
      · rw [hs]; linarith
    · have e : Hf cs zs (n + 1) xs m ys = m := by simp only [Hf, ← hi, if_neg hm]
      rw [e]
      have : (0:ℝ) ≤ ((n + 1 : ℕ) : ℝ) * cs := by positivity
      have : 0 ≤ ∑ k, |xs k + ys k| := Finset.sum_nonneg fun k _ => abs_nonneg _
      constructor
      · linarith
      · linarith [le_abs_self m]

end SDQd

namespace SDQd

variable (M : SDModel)

lemma integrable_Hf (hM : M.Standing) (zs : ℝ → ℝ) {n : ℕ} (xs : Fin n → ℝ) (m : ℝ) :
    Integrable (fun ys => Hf M.cs zs n xs m ys) (ν M xs) := by
  refine Integrable.mono' ((integrable_const (|m| + n * M.cs)).add
    (integrable_finset_sum Finset.univ fun k _ => (integrable_coord M hM xs k).abs))
    ((Hf_measurable M.cs zs n xs).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ys => ?_)
  obtain ⟨h1, h2⟩ := Hf_bounds M.cs hM.cs_pos.le zs n xs m ys
  have : (0:ℝ) ≤ n * M.cs := by have := hM.cs_pos; positivity
  have h0 : 0 ≤ ∑ k, |xs k + ys k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  simp only [Real.norm_eq_abs, Function.comp_apply, Pi.add_apply, Finset.sum_apply]
  rw [abs_le]
  constructor
  · linarith [neg_abs_le m]
  · linarith

theorem pistar_value (hM : M.Standing) (zs : ℝ → ℝ) (hzs : ∀ x, M.Qs x (zs x) = 0) :
    ∀ (n : ℕ) (xs : Fin n → ℝ) (m : ℝ),
      ∫ ys, Hf M.cs zs n xs m ys ∂ν M xs = ∫ ys, W zs m xs ys ∂ν M xs := by
  intro n
  induction n with
  | zero =>
    intro xs m
    have : ∀ ys : Fin 0 → ℝ, Hf M.cs zs 0 xs m ys = W zs m xs ys := fun ys => by
      simp [Hf, W, Wg]
    simp only [this]
  | succ n ih =>
    intro xs m
    set i := bestFin (zs ∘ xs) with hi
    by_cases hm : m < zs (xs i)
    · set xs' := xs ∘ i.succAbove with hxs'
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
      have hmp : MeasurePreserving e (ν M xs) ((M.κ (xs i)).prod (ν M xs')) := split_mp M xs i
      set G : ℝ × (Fin n → ℝ) → ℝ := fun q => Hf M.cs zs n xs' (max m (xs i + q.1)) q.2 with hG
      have hHe : ∀ ys, Hf M.cs zs (n + 1) xs m ys = G (e ys) - M.cs := by
        intro ys
        simp only [Hf, ← hi, if_pos hm]
        rfl
      have hGm : Measurable G :=
        (Hf_measurable M.cs zs n xs').comp ((measurable_const.max (measurable_const.add
          measurable_fst)).prodMk measurable_snd)
      have hv : Integrable (fun q : ℝ × (Fin n → ℝ) =>
          (|m| + n * M.cs + |xs i + q.1|) + ∑ k, |xs' k + q.2 k|)
          ((M.κ (xs i)).prod (ν M xs')) :=
        ((integrable_const _).add ((((integrable_const (xs i)).add
          (integrable_y M hM _)).abs).comp_fst _)).add
          ((integrable_finset_sum Finset.univ fun k _ =>
            (integrable_coord M hM xs' k).abs).comp_snd _ |>.congr
            (Filter.Eventually.of_forall fun q => by simp))
      have hGint : Integrable G ((M.κ (xs i)).prod (ν M xs')) := by
        refine Integrable.mono' hv hGm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun q => ?_)
        obtain ⟨h1, h2⟩ := Hf_bounds M.cs hM.cs_pos.le zs n xs' (max m (xs i + q.1)) q.2
        have : (0:ℝ) ≤ n * M.cs := by have := hM.cs_pos; positivity
        have h0 : 0 ≤ ∑ k, |xs' k + q.2 k| := Finset.sum_nonneg fun k _ => abs_nonneg _
        have h3 : |max m (xs i + q.1)| ≤ |m| + |xs i + q.1| := by
          rw [abs_le]; constructor
          · linarith [neg_abs_le m, le_max_left m (xs i + q.1), abs_nonneg (xs i + q.1)]
          · exact max_le (by linarith [le_abs_self m, abs_nonneg (xs i + q.1)])
              (by linarith [le_abs_self (xs i + q.1), abs_nonneg m])
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · linarith [neg_abs_le m, le_max_left m (xs i + q.1), abs_nonneg (xs i + q.1)]
        · linarith
      set H : ℝ × (Fin n → ℝ) → ℝ := fun q => max (xs i + q.1) (W zs m xs' q.2) with hH
      set K : ℝ × (Fin n → ℝ) → ℝ :=
        fun q => max (min (zs (xs i)) (xs i + q.1)) (W zs m xs' q.2) with hK
      have hWm := W_measurable' zs m xs'
      have hHm : Measurable H :=
        (measurable_const.add measurable_fst).max (hWm.comp measurable_snd)
      have hKm : Measurable K :=
        (measurable_const.min (measurable_const.add measurable_fst)).max (hWm.comp measurable_snd)
      have hv2 : Integrable (fun q : ℝ × (Fin n → ℝ) => |xs i + q.1| + |W zs m xs' q.2|)
          ((M.κ (xs i)).prod (ν M xs')) :=
        (((integrable_const (xs i)).add (integrable_y M hM _)).abs.comp_fst _).add
          ((integrable_W M hM zs m xs').abs.comp_snd _)
      have hHint : Integrable H ((M.κ (xs i)).prod (ν M xs')) := by
        refine Integrable.mono' hv2 hHm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun q => ?_)
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have := le_max_right (xs i + q.1) (W zs m xs' q.2)
          have := neg_abs_le (W zs m xs' q.2)
          have := abs_nonneg (xs i + q.1)
          linarith
        · refine max_le ?_ ?_
          · linarith [le_abs_self (xs i + q.1), abs_nonneg (W zs m xs' q.2)]
          · linarith [le_abs_self (W zs m xs' q.2), abs_nonneg (xs i + q.1)]
      have hKint : Integrable K ((M.κ (xs i)).prod (ν M xs')) := by
        refine Integrable.mono' hv2 hKm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun q => ?_)
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have := le_max_right (min (zs (xs i)) (xs i + q.1)) (W zs m xs' q.2)
          have := neg_abs_le (W zs m xs' q.2)
          have := abs_nonneg (xs i + q.1)
          linarith
        · refine max_le ?_ ?_
          · linarith [min_le_right (zs (xs i)) (xs i + q.1), le_abs_self (xs i + q.1),
              abs_nonneg (W zs m xs' q.2)]
          · linarith [le_abs_self (W zs m xs' q.2), abs_nonneg (xs i + q.1)]
      -- the computation
      have s1 : ∫ ys, Hf M.cs zs (n + 1) xs m ys ∂ν M xs =
          (∫ q, G q ∂(M.κ (xs i)).prod (ν M xs')) - M.cs := by
        have hGe : Integrable (fun ys => G (e ys)) (ν M xs) :=
          (hmp.integrable_comp_emb e.measurableEmbedding).mpr hGint
        rw [show (fun ys => Hf M.cs zs (n + 1) xs m ys) = fun ys => G (e ys) - M.cs from
          funext hHe, integral_sub hGe (integrable_const _), hmp.integral_comp' G]
        simp
      have s2 : ∫ q, G q ∂(M.κ (xs i)).prod (ν M xs') = ∫ q, H q ∂(M.κ (xs i)).prod (ν M xs') := by
        rw [integral_prod G hGint, integral_prod H hHint]
        congr 1; funext y
        rw [ih xs' (max m (xs i + y))]
        simp only [hH, W_max]
      have hR : ∀ ys' : Fin n → ℝ, W zs m xs' ys' ≤ zs (xs i) := by
        intro ys'
        rw [W, Wg_le_iff]
        refine ⟨hm.le, fun k => (min_le_left _ _).trans ?_⟩
        exact bestFin_spec (zs ∘ xs) (i.succAbove k)
      have s3 : ∫ q, H q ∂(M.κ (xs i)).prod (ν M xs') =
          (∫ q, K q ∂(M.κ (xs i)).prod (ν M xs')) + M.cs := by
        have hadd : ∫ ys', (∫ y, K (y, ys') ∂M.κ (xs i) + M.cs) ∂ν M xs' =
            (∫ ys', ∫ y, K (y, ys') ∂M.κ (xs i) ∂ν M xs') + M.cs := by
          rw [integral_add hKint.integral_prod_right (integrable_const _)]; simp
        rw [integral_prod_symm H hHint, integral_prod_symm K hKint, ← hadd]
        congr 1; funext ys'
        have hKy : Integrable (fun y => K (y, ys')) (M.κ (xs i)) := by
          show Integrable (fun y => max (min (zs (xs i)) (xs i + y)) (W zs m xs' ys')) _
          exact ((integrable_const _).inf ((integrable_const (xs i)).add
            (integrable_y M hM _))).sup (integrable_const _)
        rw [← excess_eq M zs hzs (xs i), ← integral_add hKy (integrable_excess M hM _ _)]
        congr 1; funext y
        exact key_eq (xs i + y) (zs (xs i)) (W zs m xs' ys') (hR ys')
      have s4 : ∫ q, K q ∂(M.κ (xs i)).prod (ν M xs') = ∫ ys, W zs m xs ys ∂ν M xs := by
        rw [← hmp.integral_comp' K]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ys => ?_)
        simp only [hK, split_apply, he]
        rw [W_split zs m xs ys i]
      rw [s1, s2, s3, s4]; ring
    · congr 1; funext ys
      have e1 : Hf M.cs zs (n + 1) xs m ys = m := by simp only [Hf, ← hi, if_neg hm]
      rw [e1]
      refine le_antisymm (le_Wg _ _) ?_
      rw [W, Wg_le_iff]
      push Not at hm
      exact ⟨le_rfl, fun k => (min_le_left _ _).trans ((bestFin_spec (zs ∘ xs) k).trans hm)⟩

end SDQd

namespace SDQd

variable (M : SDModel)

/-- The hidden values of the first `n` initial awareness products. -/
def projn (n : ℕ) (ω : M.Ω) : Fin n → ℝ := fun k => ω.1 k

lemma projn_measurable (n : ℕ) : Measurable (projn M n) :=
  measurable_pi_iff.mpr fun k => (measurable_pi_apply (k : ℕ)).comp measurable_fst

lemma initRun_eq {n : ℕ} (z : ℝ) (xs : Fin n → ℝ) (ω : M.Ω) :
    M.initRun ⟨[z], List.ofFn xs, false⟩ ω = st [z] xs (projn M n ω) 0 := by
  simp only [SDModel.initRun, st, RunState.mk.injEq, true_and, and_true]
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp [projn]

/-- Splicing a finite tuple in front of a sequence. -/
def join (n : ℕ) (p : (Fin n → ℝ) × (ℕ → ℝ)) : ℕ → ℝ :=
  fun i => if h : i < n then p.1 ⟨i, h⟩ else p.2 i

lemma join_measurable (n : ℕ) : Measurable (join n) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : i < n
  · simp only [join, h, dif_pos]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [join, h, dif_neg, not_false_eq_true]
    exact (measurable_pi_apply _).comp measurable_snd

/-- The law of the hidden values of the initial awareness products. -/
noncomputable def μs {n : ℕ} (xs : Fin n → ℝ) : ℕ → Measure ℝ :=
  fun i => M.κ ((List.ofFn xs).getD i 0)

instance {n : ℕ} (xs : Fin n → ℝ) (i : ℕ) : IsProbabilityMeasure (μs M xs i) := by
  unfold μs; infer_instance

lemma μs_lt {n : ℕ} (xs : Fin n → ℝ) (k : Fin n) : μs M xs k = M.κ (xs k) := by
  simp [μs, List.getD_eq_getElem _ _ (by simp : (k : ℕ) < (List.ofFn xs).length)]

lemma map_join {n : ℕ} (xs : Fin n → ℝ) :
    ((ν M xs).prod (Measure.infinitePi (μs M xs))).map (join n) =
      Measure.infinitePi (μs M xs) := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply (join_measurable n) (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : join n ⁻¹' Set.pi (↑s) t =
      (Set.pi Set.univ fun k : Fin n => if (k : ℕ) ∈ s then t k else Set.univ) ×ˢ
        Set.pi (↑(s.filter fun i => ¬ i < n)) t := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, join, Set.mem_prod,
      Set.mem_univ, true_implies, Finset.mem_filter]
    constructor
    · intro h
      refine ⟨fun k => ?_, fun i ⟨hi, hn⟩ => ?_⟩
      · split_ifs with hk
        · have := h k hk
          rwa [dif_pos k.2] at this
        · trivial
      · have := h i hi
        rwa [dif_neg hn] at this
    · rintro ⟨h1, h2⟩ i hi
      split_ifs with hn
      · have := h1 ⟨i, hn⟩
        rwa [if_pos hi] at this
      · exact h2 i ⟨hi, hn⟩
  rw [hpre, Measure.prod_prod, ν, Measure.pi_pi, Measure.infinitePi_pi _ (fun i _ => ht i)]
  have h1 : ∏ k : Fin n, M.κ (xs k) (if (k : ℕ) ∈ s then t k else Set.univ) =
      ∏ i ∈ s.filter (fun i => i < n), μs M xs i (t i) := by
    have : ∀ k : Fin n, M.κ (xs k) (if (k : ℕ) ∈ s then t k else Set.univ) =
        (fun i : ℕ => if i ∈ s ∧ i < n then μs M xs i (t i) else 1) k := by
      intro k
      simp only [k.2, and_true]
      split_ifs <;> simp [μs_lt]
    rw [Finset.prod_congr rfl fun k _ => this k,
      Fin.prod_univ_eq_prod_range (fun i => if i ∈ s ∧ i < n then μs M xs i (t i) else 1) n,
      ← Finset.prod_filter]
    congr 1
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; tauto
  rw [h1, Finset.prod_filter_mul_prod_filter_not]

lemma P_eq {n : ℕ} (z : ℝ) (xs : Fin n → ℝ) :
    M.P ⟨[z], List.ofFn xs, false⟩ = (Measure.infinitePi (μs M xs)).prod
      (Measure.infinitePi fun _ : ℕ =>
        (Measure.pi fun _ : Fin M.nd => M.G ⊗ₘ M.κ).prod (bernoulliBool M.q)) := rfl

lemma map_projn {n : ℕ} (z : ℝ) (xs : Fin n → ℝ) :
    (M.P ⟨[z], List.ofFn xs, false⟩).map (projn M n) = ν M xs := by
  have hr : Measurable fun f : ℕ → ℝ => fun k : Fin n => f k :=
    measurable_pi_iff.mpr fun k => measurable_pi_apply _
  have e1 : projn M n = (fun f : ℕ → ℝ => fun k : Fin n => f k) ∘ Prod.fst := rfl
  rw [e1, ← Measure.map_map hr measurable_fst, P_eq, Measure.map_fst_prod, measure_univ,
    one_smul, ← map_join M xs, Measure.map_map hr (join_measurable n)]
  have e2 : (fun f : ℕ → ℝ => fun k : Fin n => f k) ∘ join n = Prod.fst := by
    funext p; funext k; simp [join, k.2]
  rw [e2, Measure.map_fst_prod, measure_univ, one_smul]

lemma transfer_integrable {n : ℕ} (z : ℝ) (xs : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hg : Integrable (fun ω => g (projn M n ω)) (M.P ⟨[z], List.ofFn xs, false⟩)) :
    Integrable g (ν M xs) := by
  rw [P_eq] at hg
  have h1 : Integrable (fun f : ℕ → ℝ => g (fun k : Fin n => f k))
      (Measure.infinitePi (μs M xs)) :=
    Integrable.of_comp_fst (f := fun f : ℕ → ℝ => g (fun k : Fin n => f k)) hg
      (IsProbabilityMeasure.ne_zero _)
  rw [← map_join M xs] at h1
  have h2 := h1.comp_measurable (join_measurable n)
  have e2 : (fun f : ℕ → ℝ => g (fun k : Fin n => f k)) ∘ join n = fun p => g p.1 := by
    funext p
    have : (fun k : Fin n => join n p k) = p.1 := by funext k; simp [join, k.2]
    simp only [Function.comp_apply, this]
  rw [e2] at h2
  exact Integrable.of_comp_fst h2 (IsProbabilityMeasure.ne_zero _)

lemma transfer_ae {n : ℕ} (z : ℝ) (xs : Fin n → ℝ) (p : (Fin n → ℝ) → Prop)
    (hp : ∀ᵐ ω ∂M.P ⟨[z], List.ofFn xs, false⟩, p (projn M n ω)) : ∀ᵐ ys ∂ν M xs, p ys := by
  rw [P_eq] at hp
  have h1 : ∀ᵐ f ∂Measure.infinitePi (μs M xs), p (fun k : Fin n => f k) := by
    have := Measure.ae_ae_of_ae_prod hp
    filter_upwards [this] with f hf
    have : (ae (Measure.infinitePi fun _ : ℕ =>
        (Measure.pi fun _ : Fin M.nd => M.G ⊗ₘ M.κ).prod (bernoulliBool M.q))).NeBot :=
      ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
    obtain ⟨d, hd⟩ := hf.exists
    exact hd
  rw [← map_join M xs] at h1
  have h2 := ae_of_ae_map (join_measurable n).aemeasurable h1
  have h3 := Measure.ae_ae_of_ae_prod h2
  filter_upwards [h3] with a ha
  have : (ae (Measure.infinitePi (μs M xs))).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨b, hb⟩ := ha.exists
  have e : (fun k : Fin n => join n (a, b) k) = a := by funext k; simp [join, k.2]
  rwa [e] at hb

lemma transfer_integral {n : ℕ} (z : ℝ) (xs : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hg : Integrable g (ν M xs)) :
    Integrable (fun ω => g (projn M n ω)) (M.P ⟨[z], List.ofFn xs, false⟩) ∧
      ∫ ω, g (projn M n ω) ∂M.P ⟨[z], List.ofFn xs, false⟩ = ∫ ys, g ys ∂ν M xs := by
  have hm := map_projn M z xs
  refine ⟨?_, ?_⟩
  · rw [← hm] at hg
    exact hg.comp_measurable (projn_measurable M n)
  · rw [← hm, integral_map (projn_measurable M n).aemeasurable (by rw [hm]; exact hg.1)]

theorem optValue_eq (hM : M.Standing) (zs : ℝ → ℝ) (hzs : ∀ x, M.Qs x (zs x) = 0) {n : ℕ}
    (z : ℝ) (xs : Fin n → ℝ) :
    M.optValue ⟨[z], List.ofFn xs, false⟩ = ∫ ys, W zs z xs ys ∂ν M xs := by
  set s : InfoState := ⟨[z], List.ofFn xs, false⟩ with hs
  have hdisc : s.disc = false := rfl
  have hz : [z].getD (bestIdx [z]) 0 = z := by
    have : bestIdx [z] = 0 := by simp [bestIdx]
    rw [this]; rfl
  have hval : ∀ π, M.value π s = ∫ ω, Φ M π (st [z] xs (projn M n ω) 0) ∂M.P s := by
    intro π
    unfold SDModel.value
    congr 1; funext ω
    rw [payoff_eq_Φ M π s ω hdisc, hs, initRun_eq]
  apply IsGreatest.csSup_eq
  refine ⟨⟨pistar zs, ?_, ?_⟩, ?_⟩
  · have hΦ : ∀ ys : Fin n → ℝ, Φ M (pistar zs) (st [z] xs ys 0) = Hf M.cs zs n xs z ys - 0 := by
      intro ys; rw [(pistar_run M zs n xs ys [z] 0 (by simp)).2, hz]
    rw [feasible_iff M _ s hdisc]
    refine ⟨Filter.Eventually.of_forall fun ω => ?_, ?_⟩
    · rw [hs, initRun_eq]; exact (pistar_run M zs n xs _ [z] 0 (by simp)).1
    · simp only [hs, initRun_eq, hΦ, sub_zero]
      exact (transfer_integral M z xs _ (integrable_Hf M hM zs xs z)).1
  · rw [hval]
    have hΦ : ∀ ys : Fin n → ℝ, Φ M (pistar zs) (st [z] xs ys 0) = Hf M.cs zs n xs z ys := by
      intro ys; rw [(pistar_run M zs n xs ys [z] 0 (by simp)).2, hz, sub_zero]
    simp only [hΦ]
    rw [(transfer_integral M z xs _ (integrable_Hf M hM zs xs z)).2, pistar_value M hM zs hzs]
  · rintro v ⟨π, hπ, rfl⟩
    rw [feasible_iff M _ s hdisc] at hπ
    obtain ⟨hG, hI⟩ := hπ
    simp only [hs, initRun_eq] at hG hI
    have hG' := transfer_ae M z xs (fun ys => Good M π (st [z] xs ys 0)) hG
    have hI' := transfer_integrable M z xs (fun ys => Φ M π (st [z] xs ys 0)) hI
    rw [hval, (transfer_integral M z xs _ hI').2]
    have := upper M hM zs hzs n xs [z] z 0 π (by simp) hG' hI'
    simpa using this

end SDQd

namespace SDQd

lemma lintegral_pi_prod : ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ k, IsProbabilityMeasure (μ k)]
    (f : Fin n → ℝ → ENNReal), (∀ k, Measurable (f k)) →
    ∫⁻ x, ∏ k, f k (x k) ∂Measure.pi μ = ∏ k, ∫⁻ y, f k y ∂μ k := by
  intro n
  induction n with
  | zero => intro μ _ f _; simp
  | succ n ih =>
    intro μ _ f hf
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hmp : MeasurePreserving e (Measure.pi μ)
        ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
      measurePreserving_piFinSuccAbove μ 0
    set G : ℝ × (Fin n → ℝ) → ENNReal :=
      fun q => f 0 q.1 * ∏ k : Fin n, f (Fin.succAbove 0 k) (q.2 k)
    have hG : ∀ x, ∏ k, f k (x k) = G (e x) := by
      intro x
      rw [Fin.prod_univ_succ]
      simp only [G, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.succAbove_zero]
      rfl
    simp_rw [hG]
    rw [hmp.lintegral_comp_emb e.measurableEmbedding G]
    show ∫⁻ q, f 0 q.1 * (fun x' : Fin n → ℝ => ∏ k : Fin n, f (Fin.succAbove 0 k) (x' k)) q.2
      ∂(μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j)) = _
    have hg : AEMeasurable (fun x' : Fin n → ℝ => ∏ k : Fin n, f (Fin.succAbove 0 k) (x' k))
        (Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
      (Finset.measurable_prod _ fun k _ => (hf _).comp (measurable_pi_apply k)).aemeasurable
    have := lintegral_prod_mul (μ := μ 0) (hf 0).aemeasurable hg
    rw [this, ih (fun j => μ (Fin.succAbove 0 j)) (fun k => f (Fin.succAbove 0 k)) (fun k => hf _),
      Fin.prod_univ_succ]
    simp only [Fin.succAbove_zero]

variable (M : SDModel)

lemma measurable_ν (n : ℕ) : Measurable fun xs : Fin n → ℝ => ν M xs := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  refine MeasurableSpace.induction_on_inter (C := fun S _ => Measurable fun xs => ν M xs S)
    generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_ S hS
  · simp
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := ht
    simp_rw [ν, Measure.pi_pi]
    exact Finset.measurable_prod _ fun k _ =>
      (M.κ.measurable_coe (hs k (Set.mem_univ k))).comp (measurable_pi_apply k)
  · intro t htm ih
    simp_rw [measure_compl htm (measure_ne_top _ _), measure_univ]
    exact measurable_const.sub ih
  · intro f hdisj hfm ih
    simp_rw [measure_iUnion hdisj hfm]
    exact Measurable.ennreal_tsum ih

/-- The kernel `xs ↦ ⊗_k F_{Y|X = x_k}`. -/
noncomputable def piK (n : ℕ) : Kernel (Fin n → ℝ) (Fin n → ℝ) where
  toFun xs := ν M xs
  measurable' := measurable_ν M n

instance (n : ℕ) : IsMarkovKernel (piK M n) :=
  ⟨fun xs => by show IsProbabilityMeasure (ν M xs); infer_instance⟩

/-- Zipping partial valuations with hidden values. -/
def zip (n : ℕ) (q : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ × ℝ := fun k => (q.1 k, q.2 k)

lemma zip_measurable (n : ℕ) : Measurable (zip n) :=
  measurable_pi_iff.mpr fun k =>
    ((measurable_pi_apply k).comp measurable_fst).prodMk ((measurable_pi_apply k).comp measurable_snd)

lemma map_zip (n : ℕ) :
    ((Measure.pi fun _ : Fin n => M.G) ⊗ₘ piK M n).map (zip n) =
      Measure.pi fun _ : Fin n => M.G ⊗ₘ M.κ := by
  refine (Measure.pi_eq fun S hS => ?_).symm
  rw [Measure.map_apply (zip_measurable n) (MeasurableSet.univ_pi hS),
    Measure.compProd_apply ((zip_measurable n) (MeasurableSet.univ_pi hS))]
  have hslice : ∀ xs : Fin n → ℝ, Prod.mk xs ⁻¹' (zip n ⁻¹' Set.univ.pi S) =
      Set.univ.pi fun k => Prod.mk (xs k) ⁻¹' S k := by
    intro xs; ext ys; simp [zip]
  simp_rw [hslice]
  have h2 : ∀ xs : Fin n → ℝ, piK M n xs (Set.univ.pi fun k => Prod.mk (xs k) ⁻¹' S k) =
      ∏ k, (fun k x => M.κ x (Prod.mk x ⁻¹' S k)) k (xs k) := by
    intro xs
    show ν M xs _ = _
    rw [ν, Measure.pi_pi]
  simp_rw [h2]
  rw [lintegral_pi_prod n (fun _ => M.G) _
    (fun k => Kernel.measurable_kernel_prodMk_left (hS k))]
  congr 1; funext k
  rw [Measure.compProd_apply (hS k)]

lemma integral_zip (n : ℕ) (F : (Fin n → ℝ × ℝ) → ℝ)
    (hF : Integrable F (Measure.pi fun _ : Fin n => M.G ⊗ₘ M.κ)) :
    ∫ p, F p ∂(Measure.pi fun _ : Fin n => M.G ⊗ₘ M.κ) =
      ∫ xs, ∫ ys, F (zip n (xs, ys)) ∂ν M xs ∂(Measure.pi fun _ : Fin n => M.G) := by
  rw [← map_zip M n] at hF ⊢
  rw [integral_map (zip_measurable n).aemeasurable hF.aestronglyMeasurable]
  rw [Measure.integral_compProd (f := fun q => F (zip n q)) (hF.comp_measurable (zip_measurable n))]
  rfl

end SDQd

theorem solution (M : SDModel) (hM : M.Standing)
    (zs : ℝ → ℝ) (hzs : ∀ x, M.Qs x (zs x) = 0) (z : ℝ) :
    let W : (Fin M.nd → ℝ × ℝ) → ℝ :=
      fun p => ⨆ k : Fin M.nd, min (zs (p k).1) ((p k).1 + (p k).2)
    let μ : Measure (Fin M.nd → ℝ × ℝ) := Measure.pi fun _ : Fin M.nd => M.G ⊗ₘ M.κ
    M.Qd z = (∫ p, max z (W p) ∂μ) - z - M.cd ∧
    M.Qd z = (∫ p, max 0 (W p - z) ∂μ) - M.cd ∧
    M.Qd z = (∫ w in Set.Ioi z, (1 - cdf (μ.map W) w)) - M.cd := by
  intro W μ
  have hnd : Nonempty (Fin M.nd) := ⟨⟨0, hM.nd_pos⟩⟩
  -- measurability of the search value
  have hgκ : ∀ x z : ℝ, Integrable (fun y : ℝ => max 0 (x + y - z)) (M.κ x) :=
    fun x z => SDQd.integrable_excess M hM x z
  have hanti : ∀ x a b, a ≤ b → M.Qs x b ≤ M.Qs x a := by
    intro x a b hab
    simp only [SDModel.Qs]
    have := integral_mono (hgκ x b) (hgκ x a) (fun y => max_le_max le_rfl (by linarith))
    linarith
  have hiff : ∀ x c, zs x ≤ c ↔ M.Qs x c ≤ 0 := by
    intro x c
    constructor
    · intro h; exact (hanti x _ _ h).trans (hzs x).le
    · intro h
      by_contra hlt
      push Not at hlt
      have h0 : M.Qs x c = 0 := le_antisymm h ((hzs x).symm.le.trans (hanti x _ _ hlt.le))
      have := (eq6_unique_solution M hM x).unique h0 (hzs x)
      linarith
  have hQm : ∀ c, Measurable fun x => M.Qs x c := by
    intro c
    have hF : StronglyMeasurable fun q : ℝ × ℝ => max 0 (q.1 + q.2 - c) :=
      (by fun_prop : Continuous fun q : ℝ × ℝ => max 0 (q.1 + q.2 - c)).stronglyMeasurable
    exact (hF.integral_kernel_prod_right' (κ := M.κ)).measurable.sub_const _
  have hzsm : Measurable zs := by
    refine measurable_of_Iic fun c => ?_
    have : zs ⁻¹' Set.Iic c = {x | M.Qs x c ≤ 0} := by
      ext x; simp [hiff]
    rw [this]
    exact measurableSet_le (hQm c) measurable_const
  have hWm : Measurable W := by
    refine Measurable.iSup fun k => ?_
    have h1 : Measurable fun p : Fin M.nd → ℝ × ℝ => (p k).1 :=
      measurable_fst.comp (measurable_pi_apply k)
    have h2 : Measurable fun p : Fin M.nd → ℝ × ℝ => (p k).2 :=
      measurable_snd.comp (measurable_pi_apply k)
    exact (hzsm.comp h1).min (h1.add h2)
  -- `max z W` is the fold `Wg`
  have hfold : ∀ p, max z (W p) = SDQd.Wg z (fun k => min (zs (p k).1) ((p k).1 + (p k).2)) := by
    intro p
    refine SDQd.eq_of_le_iff fun c => ?_
    rw [max_le_iff, SDQd.Wg_le_iff]
    simp only [W]
    rw [ciSup_le_iff (Set.finite_range _).bddAbove]
  -- integrability
  set ν' := M.G ⊗ₘ M.κ with hν'
  have hfst : ν'.map Prod.fst = M.G := by
    rw [← Measure.fst, hν', Measure.fst_compProd]
  have hX : Integrable (fun q : ℝ × ℝ => q.1) ν' := by
    have hG : Integrable (fun x : ℝ => x) M.G := hM.memLp_G.integrable (by norm_num)
    rw [← hfst] at hG
    exact hG.comp_measurable measurable_fst
  have hv : Integrable (fun q : ℝ × ℝ => q.1 + q.2) ν' := hX.add hM.integrable_Y
  have hvk : ∀ k : Fin M.nd, Integrable (fun p : Fin M.nd → ℝ × ℝ => |(p k).1 + (p k).2|) μ := by
    intro k
    have hmp : MeasurePreserving (Function.eval k) μ ν' := measurePreserving_eval _ k
    exact hmp.integrable_comp_of_integrable hv.abs
  have hmaxm : Measurable fun p => max z (W p) := measurable_const.max hWm
  have hint1 : Integrable (fun p => max z (W p)) μ := by
    refine Integrable.mono' ((integrable_const |z|).add
      (integrable_finset_sum Finset.univ fun k _ => hvk k)) hmaxm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, hfold]
    simpa using SDQd.abs_Wg_le z _ (fun k => (p k).1 + (p k).2) (fun k => min_le_right _ _)
  have hQd : M.Qd z = (∫ p, max z (W p) ∂μ) - z - M.cd := by
    unfold SDModel.Qd
    congr 2
    rw [SDQd.integral_zip M M.nd _ hint1]
    congr 1; funext xs
    rw [SDQd.optValue_eq M hM zs hzs z xs]
    congr 1; funext ys
    rw [hfold]
    rfl
  have hpt : ∀ p, max 0 (W p - z) = max z (W p) - z := by
    intro p
    rcases le_total z (W p) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  have hint2 : Integrable (fun p => max 0 (W p - z)) μ := by
    have := hint1.sub (integrable_const z)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply, hpt]
  have h2 : ∫ p, max 0 (W p - z) ∂μ = (∫ p, max z (W p) ∂μ) - z := by
    simp only [hpt]
    rw [integral_sub hint1 (integrable_const z)]
    simp
  refine ⟨hQd, by rw [hQd, h2], ?_⟩
  rw [hQd, ← h2]
  congr 1
  have : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hWm.aemeasurable
  rw [hint2.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun p => le_max_left _ _)]
  have h3 : ∫ t in Set.Ioi (0:ℝ), μ.real {p | t < max 0 (W p - z)} =
      ∫ t in Set.Ioi (0:ℝ), (1 - cdf (μ.map W) (t + z)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [Set.mem_Ioi] at ht
    have hset : {p | t < max 0 (W p - z)} = W ⁻¹' (Set.Iic (t + z))ᶜ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_Iic, not_le,
        lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h; right; linarith
    rw [hset, ← map_measureReal_apply hWm measurableSet_Iic.compl,
      measureReal_compl measurableSet_Iic, cdf_eq_real]
    simp
  rw [h3]
  have h4 := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (Set.indicator (Set.Ioi z) (fun w => 1 - cdf (μ.map W) w)) z
  rw [integral_indicator measurableSet_Ioi] at h4
  rw [← h4, ← integral_indicator measurableSet_Ioi]
  congr 1; funext t
  by_cases ht : t ∈ Set.Ioi (0:ℝ)
  · have : t + z ∈ Set.Ioi z := by simp only [Set.mem_Ioi] at ht ⊢; linarith
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem this]
  · have : t + z ∉ Set.Ioi z := by simp only [Set.mem_Ioi, not_lt] at ht ⊢; linarith
    rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem this]
