-- Prove2me | solution 1 for SearchDiscovery.Reservation.search_value_gittins_index
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:14:02.148998+00:00
-- url     : https://prove2.me/submissions/b34902eb-72c7-4ea0-8ab7-253bd5b38f41

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

open SearchDiscovery.Reservation MeasureTheory ProbabilityTheory

namespace SDGittinsAux

lemma run_succ (M : SDModel) (π : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) (t : ℕ) :
    M.run π s₀ ω (t + 1) = M.step π ω (M.run π s₀ ω t) := by
  simp only [SDModel.run]
  rw [Function.iterate_succ_apply']

lemma run_zero (M : SDModel) (π : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) :
    M.run π s₀ ω 0 = M.initRun s₀ ω := rfl

lemma step_of_bought (M : SDModel) (π : InfoState → Act) (ω : M.Ω) (r : RunState) (b : ℝ)
    (h : r.bought = some b) : M.step π ω r = r := by
  simp [SDModel.step, h]

lemma run_frozen (M : SDModel) (π : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) (n : ℕ) (b : ℝ)
    (h : (M.run π s₀ ω n).bought = some b) : ∀ k, M.run π s₀ ω (n + k) = M.run π s₀ ω n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, run_succ, ih, step_of_bought M π ω _ b h]

lemma payoff_eq (M : SDModel) (π : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) (n : ℕ) (b : ℝ)
    (hn : (M.run π s₀ ω n).bought = some b)
    (hlt : ∀ m < n, (M.run π s₀ ω m).bought = none) :
    M.payoff π s₀ ω = b - (M.run π s₀ ω n).cost := by
  classical
  have h : ∃ t, (M.run π s₀ ω t).bought.isSome := ⟨n, by simp [hn]⟩
  have hf : Nat.find h = n := by
    rw [Nat.find_eq_iff]
    refine ⟨by simp [hn], fun m hm => by simp [hlt m hm]⟩
  unfold SDModel.payoff
  rw [dif_pos h]
  simp only [hf, hn, Option.getD_some]

instance (M : SDModel) (s₀ : InfoState) : IsProbabilityMeasure (M.P s₀) := by
  unfold SDModel.P; infer_instance

lemma info_initRun (M : SDModel) (s₀ : InfoState) (ω : M.Ω) : (M.initRun s₀ ω).info = s₀ := by
  rcases s₀ with ⟨C, S, d⟩
  simp only [SDModel.initRun, RunState.info, InfoState.mk.injEq, true_and, and_true]
  apply List.ext_getElem <;> simp

lemma avail_zero (M : SDModel) (ρ : InfoState → Act) (s₀ : InfoState) (h : M.Feasible ρ s₀) :
    Available s₀ (ρ s₀) := by
  have : (ae (M.P s₀)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨ω, hω⟩ := h.1.exists
  have := hω 0 rfl
  rwa [run_zero, info_initRun] at this

lemma run_one_buy (M : SDModel) (ρ : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) (i : ℕ)
    (hρ : ρ s₀ = .buy i) (hi : i < s₀.C.length) :
    M.run ρ s₀ ω 1 = { M.initRun s₀ ω with bought := some s₀.C[i] } := by
  rw [run_succ, run_zero]
  have hb : (M.initRun s₀ ω).bought = none := rfl
  simp only [SDModel.step, hb, info_initRun, hρ]
  rw [dif_pos (show i < (M.initRun s₀ ω).C.length from hi)]
  rfl

lemma payoff_buy (M : SDModel) (ρ : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) (i : ℕ)
    (hρ : ρ s₀ = .buy i) (hi : i < s₀.C.length) :
    M.payoff ρ s₀ ω = s₀.C[i] := by
  rw [payoff_eq M ρ s₀ ω 1 s₀.C[i] (by rw [run_one_buy M ρ s₀ ω i hρ hi])
    (fun m hm => by interval_cases m; rfl), run_one_buy M ρ s₀ ω i hρ hi]
  simp [SDModel.initRun]

lemma feasible_buy (M : SDModel) (ρ : InfoState → Act) (s₀ : InfoState) (i : ℕ)
    (hρ : ρ s₀ = .buy i) (hi : i < s₀.C.length) : M.Feasible ρ s₀ ∧ M.value ρ s₀ = s₀.C[i] := by
  have hpay : M.payoff ρ s₀ = fun _ => s₀.C[i] := funext fun ω => payoff_buy M ρ s₀ ω i hρ hi
  refine ⟨⟨Filter.Eventually.of_forall fun ω t ht => ?_,
    Filter.Eventually.of_forall fun ω => ⟨1, by rw [run_one_buy M ρ s₀ ω i hρ hi]; rfl⟩, ?_⟩, ?_⟩
  · rcases t with _ | t
    · rw [run_zero, info_initRun, hρ]; exact hi
    · exfalso
      have h1 : (M.run ρ s₀ ω 1).bought = some s₀.C[i] := by
        rw [run_one_buy M ρ s₀ ω i hρ hi]
      have := run_frozen M ρ s₀ ω 1 _ h1 t
      rw [add_comm 1 t] at this
      rw [this, h1] at ht
      cases ht
  · rw [hpay]; exact integrable_const _
  · unfold SDModel.value; rw [hpay]; simp

lemma run_succ_buy (M : SDModel) (ρ : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) (t j : ℕ)
    (hb : (M.run ρ s₀ ω t).bought = none) (hρ : ρ (M.run ρ s₀ ω t).info = .buy j)
    (hj : j < (M.run ρ s₀ ω t).C.length) :
    M.run ρ s₀ ω (t + 1) = { M.run ρ s₀ ω t with bought := some (M.run ρ s₀ ω t).C[j] } := by
  rw [run_succ]
  simp only [SDModel.step, hb, hρ]
  rw [dif_pos hj]

/-- The policy "inspect the first awareness product; once nothing is left to inspect, buy the
better of the first two products of the consideration set". -/
noncomputable def rstar (s : InfoState) : Act :=
  match s.S with
  | [] => if s.C.getD 0 0 < s.C.getD 1 0 then .buy 1 else .buy 0
  | _ :: _ => .inspect 0

lemma run_one_inspect (M : SDModel) (ρ : InfoState → Act) (w x : ℝ) (ω : M.Ω)
    (hρ : ρ ⟨[w], [x], false⟩ = .inspect 0) :
    M.run ρ ⟨[w], [x], false⟩ ω 1 = ⟨[w, x + ω.1 0], [], false, 0, 0 + M.cs, none⟩ := by
  rw [run_succ, run_zero]
  have hb : (M.initRun ⟨[w], [x], false⟩ ω).bought = none := rfl
  simp only [SDModel.step, hb, info_initRun, hρ]
  rw [dif_pos (show 0 < (M.initRun ⟨[w], [x], false⟩ ω).S.length by simp [SDModel.initRun])]
  simp [SDModel.initRun]

lemma payoff_inspect_buy (M : SDModel) (ρ : InfoState → Act) (w x : ℝ) (ω : M.Ω)
    (hρ : ρ ⟨[w], [x], false⟩ = .inspect 0) (j : ℕ)
    (hj : ρ ⟨[w, x + ω.1 0], [], false⟩ = .buy j) (hj2 : j < 2) :
    M.payoff ρ ⟨[w], [x], false⟩ ω = [w, x + ω.1 0][j] - (0 + M.cs) := by
  have h1 := run_one_inspect M ρ w x ω hρ
  have hinfo : (M.run ρ ⟨[w], [x], false⟩ ω 1).info = ⟨[w, x + ω.1 0], [], false⟩ := by
    rw [h1]; rfl
  have h2 := run_succ_buy M ρ _ ω 1 j (by rw [h1]) (by rw [hinfo, hj]) (by rw [h1]; exact hj2)
  rw [payoff_eq M ρ _ ω 2 [w, x + ω.1 0][j] (by rw [h2]; simp [h1])
    (fun m hm => by interval_cases m <;> [rfl; rw [h1]])]
  congr 1
  rw [h2]
  show (M.run ρ _ ω 1).cost = _
  rw [h1]

lemma measPres (M : SDModel) (w x : ℝ) :
    MeasurePreserving (fun ω : M.Ω => ω.1 0) (M.P ⟨[w], [x], false⟩) (M.κ x) := by
  have h1 := measurePreserving_eval_infinitePi
    (fun i : ℕ => M.κ ((⟨[w], [x], false⟩ : InfoState).S.getD i 0)) 0
  have h2 : MeasurePreserving (Prod.fst : M.Ω → (ℕ → ℝ)) (M.P ⟨[w], [x], false⟩)
      (Measure.infinitePi fun i : ℕ => M.κ ((⟨[w], [x], false⟩ : InfoState).S.getD i 0)) := by
    unfold SDModel.P; exact measurePreserving_fst
  exact h1.comp h2

end SDGittinsAux

open SDGittinsAux

theorem solution (M : SDModel) (hM : M.Standing)
    (zs : ℝ → ℝ) (hzs : ∀ x, M.Qs x (zs x) = 0) (w x v : ℝ) :
    ((∀ ρ : InfoState → Act, M.Feasible ρ ⟨[w], [x], false⟩ →
        M.value ρ ⟨[w], [x], false⟩ ≤ w) ↔ zs x ≤ w) ∧
    ((∀ ρ : InfoState → Act, M.Feasible ρ ⟨[w, v], [], false⟩ →
        M.value ρ ⟨[w, v], [], false⟩ ≤ w) ↔ v ≤ w) := by
  have hcs := hM.cs_pos
  set μ := M.κ x with hμ
  have hint : Integrable (fun y : ℝ => y) μ :=
    (hM.memLp_κ x).integrable (by norm_num)
  have hg : ∀ z : ℝ, Integrable (fun y : ℝ => max 0 (x + y - z)) μ := by
    intro z
    have h1 : Integrable (fun y : ℝ => x + y - z) μ :=
      ((integrable_const x).add hint).sub (integrable_const z)
    exact (integrable_const (0:ℝ)).sup h1
  set f : ℝ → ℝ := fun z => ∫ y, max 0 (x + y - z) ∂μ with hf
  have hQ : ∀ z, M.Qs x z = f z - M.cs := fun z => rfl
  have hanti : ∀ a b, a ≤ b → f b ≤ f a := fun a b hab =>
    integral_mono (hg b) (hg a) (fun y => max_le_max le_rfl (by linarith))
  have hstrict : ∀ a b, a < b → f a = f b → f b = 0 := by
    intro a b hab heq
    have hd : ∫ y, (max 0 (x + y - a) - max 0 (x + y - b)) ∂μ = 0 := by
      rw [integral_sub (hg a) (hg b)]; exact sub_eq_zero.mpr heq
    have hnn : 0 ≤ᵐ[μ] fun y => max 0 (x + y - a) - max 0 (x + y - b) :=
      Filter.Eventually.of_forall fun y => by
        simp only [Pi.zero_apply, sub_nonneg]
        exact max_le_max le_rfl (by linarith)
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn ((hg a).sub (hg b))).mp hd
    have : (fun y => max 0 (x + y - b)) =ᵐ[μ] fun _ => (0:ℝ) := by
      filter_upwards [hae] with y hy
      simp only [Pi.zero_apply] at hy
      by_contra hne
      have hpos : 0 < x + y - b := by
        by_contra h; push Not at h; exact hne (max_eq_left h)
      rw [max_eq_right hpos.le, max_eq_right (by linarith : (0:ℝ) ≤ x + y - a)] at hy
      linarith
    show ∫ y, max 0 (x + y - b) ∂μ = 0
    rw [integral_congr_ae this]; simp
  -- the integral of `max w (x + Y) - c_s`
  set g : ℝ → ℝ := fun y => max w (x + y) - (0 + M.cs) with hgdef
  have hgint : Integrable g μ :=
    ((integrable_const w).sup ((integrable_const x).add hint)).sub (integrable_const _)
  have hgval : ∫ y, g y ∂μ = w + f w - M.cs := by
    have : g = fun y => w + max 0 (x + y - w) - M.cs := by
      funext y
      simp only [hgdef]
      rcases le_total w (x + y) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
    have hI : Integrable (fun y => w + max 0 (x + y - w)) μ := (integrable_const w).add (hg w)
    rw [show (∫ y, g y ∂μ) = ∫ y, (w + max 0 (x + y - w) - M.cs) ∂μ from by rw [this],
      integral_sub hI (integrable_const _), integral_add (integrable_const w) (hg w)]
    simp [hf]
  have hφ : MeasurePreserving (fun ω : M.Ω => ω.1 0) (M.P ⟨[w], [x], false⟩) μ := measPres M w x
  have hgP : Integrable (fun ω : M.Ω => g (ω.1 0)) (M.P ⟨[w], [x], false⟩) :=
    hφ.integrable_comp_of_integrable hgint
  have hgPval : ∫ ω, g (ω.1 0) ∂(M.P ⟨[w], [x], false⟩) = w + f w - M.cs := by
    rw [← hgval, ← hφ.map_eq, integral_map hφ.measurable.aemeasurable]
    rw [hφ.map_eq]; exact hgint.aestronglyMeasurable
  refine ⟨⟨fun h => ?_, fun hle ρ hρ => ?_⟩, ⟨fun h => ?_, fun hv ρ hρ => ?_⟩⟩
  · -- the policy `rstar` attains `w + Q_s(x, c_s, w)`
    by_contra hlt
    push Not at hlt
    have hfz : f (zs x) = M.cs := by have := hzs x; rw [hQ] at this; linarith
    have hfw : M.cs < f w := by
      rcases (hanti w (zs x) hlt.le).lt_or_eq with h' | h'
      · linarith
      · have := hstrict w (zs x) hlt h'.symm; linarith
    have hpay : M.payoff rstar ⟨[w], [x], false⟩ = fun ω => g (ω.1 0) := by
      funext ω
      by_cases hwu : w < x + ω.1 0
      · rw [payoff_inspect_buy M rstar w x ω rfl 1 (by simp [rstar, hwu]) (by norm_num)]
        simp [hgdef, max_eq_right hwu.le]
      · push Not at hwu
        rw [payoff_inspect_buy M rstar w x ω rfl 0
          (by simp [rstar, not_lt.mpr hwu]) (by norm_num)]
        simp [hgdef, max_eq_left hwu]
    have hfeas : M.Feasible rstar ⟨[w], [x], false⟩ := by
      refine ⟨Filter.Eventually.of_forall fun ω t ht => ?_,
        Filter.Eventually.of_forall fun ω => ⟨2, ?_⟩, by rw [hpay]; exact hgP⟩
      · have h1 := run_one_inspect M rstar w x ω rfl
        rcases t with _ | _ | t
        · rw [run_zero, info_initRun]; show (0:ℕ) < 1; norm_num
        · rw [zero_add, h1]
          show Available ⟨[w, x + ω.1 0], [], false⟩ (rstar ⟨[w, x + ω.1 0], [], false⟩)
          by_cases hwu : w < x + ω.1 0
          · simp [rstar, hwu, Available]
          · simp [rstar, hwu, Available]
        · exfalso
          have hinfo : (M.run rstar ⟨[w], [x], false⟩ ω 1).info = ⟨[w, x + ω.1 0], [], false⟩ := by
            rw [h1]; rfl
          have hb2 : ∃ b, (M.run rstar ⟨[w], [x], false⟩ ω 2).bought = some b := by
            by_cases hwu : w < x + ω.1 0
            · have h2 := run_succ_buy M rstar _ ω 1 1 (by rw [h1])
                (by rw [hinfo]; simp [rstar, hwu]) (by rw [h1]; simp)
              exact ⟨_, by rw [h2]⟩
            · have h2 := run_succ_buy M rstar _ ω 1 0 (by rw [h1])
                (by rw [hinfo]; simp [rstar, hwu]) (by rw [h1]; simp)
              exact ⟨_, by rw [h2]⟩
          obtain ⟨b, hb⟩ := hb2
          have := run_frozen M rstar _ ω 2 b hb t
          rw [show t + 1 + 1 = 2 + t by ring, this, hb] at ht
          cases ht
      · have h1 := run_one_inspect M rstar w x ω rfl
        have hinfo : (M.run rstar ⟨[w], [x], false⟩ ω 1).info = ⟨[w, x + ω.1 0], [], false⟩ := by
          rw [h1]; rfl
        by_cases hwu : w < x + ω.1 0
        · have h2 := run_succ_buy M rstar _ ω 1 1 (by rw [h1])
            (by rw [hinfo]; simp [rstar, hwu]) (by rw [h1]; simp)
          rw [h2]; rfl
        · have h2 := run_succ_buy M rstar _ ω 1 0 (by rw [h1])
            (by rw [hinfo]; simp [rstar, hwu]) (by rw [h1]; simp)
          rw [h2]; rfl
    have hval := h rstar hfeas
    unfold SDModel.value at hval
    rw [hpay, hgPval] at hval
    linarith
  · -- every feasible policy earns at most `w + Q_s(x, c_s, w) ≤ w`
    have hfz : f (zs x) = M.cs := by have := hzs x; rw [hQ] at this; linarith
    have hfw : f w ≤ M.cs := hfz ▸ hanti _ _ hle
    have ha := avail_zero M ρ _ hρ
    cases hc : ρ ⟨[w], [x], false⟩ with
    | buy i =>
      rw [hc] at ha
      have hi : i < 1 := ha
      rw [(feasible_buy M ρ _ i hc hi).2]
      interval_cases i; simp
    | discover => rw [hc] at ha; exact absurd ha (by simp [Available])
    | inspect i =>
      rw [hc] at ha
      have hi : i < 1 := ha
      interval_cases i
      have hbound : ∀ᵐ ω ∂(M.P ⟨[w], [x], false⟩), M.payoff ρ ⟨[w], [x], false⟩ ω ≤ g (ω.1 0) := by
        filter_upwards [hρ.1] with ω hω
        have h1 := run_one_inspect M ρ w x ω hc
        have hav := hω 1 (by rw [h1])
        have hinfo : (M.run ρ ⟨[w], [x], false⟩ ω 1).info = ⟨[w, x + ω.1 0], [], false⟩ := by
          rw [h1]; rfl
        rw [hinfo] at hav
        cases hc2 : ρ ⟨[w, x + ω.1 0], [], false⟩ with
        | buy j =>
          rw [hc2] at hav
          have hj : j < 2 := hav
          rw [payoff_inspect_buy M ρ w x ω hc j hc2 hj]
          simp only [hgdef]
          interval_cases j
          · simp
          · simp
        | inspect j => rw [hc2] at hav; exact absurd hav (by simp [Available])
        | discover => rw [hc2] at hav; exact absurd hav (by simp [Available])
      have := integral_mono_ae hρ.2.2 hgP hbound
      unfold SDModel.value
      rw [hgPval] at this
      linarith
  · have := feasible_buy M (fun _ => Act.buy 1) ⟨[w, v], [], false⟩ 1 rfl (by simp)
    have h' := h _ this.1
    rw [this.2] at h'
    simpa using h'
  · have ha := avail_zero M ρ _ hρ
    cases hc : ρ ⟨[w, v], [], false⟩ with
    | buy i =>
      rw [hc] at ha
      have hi : i < 2 := ha
      rw [(feasible_buy M ρ _ i hc hi).2]
      interval_cases i
      · simp
      · simpa using hv
    | inspect i => rw [hc] at ha; exact absurd ha (by simp [Available])
    | discover => rw [hc] at ha; exact absurd ha (by simp [Available])
