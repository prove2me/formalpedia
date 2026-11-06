-- Prove2me | solution 1 for TabooRegen.delay_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T17:06:46.754614+00:00
-- url     : https://prove2.me/submissions/da762481-2e44-49d7-8ae0-c8b60b5c0326

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace TabooRegen.DelayShift

open TabooRegen TabooRegen.Model

/-- dyadic upper approximation of a time -/
noncomputable def dyUp (m : ℕ) (s : ℝ≥0) : ℝ≥0 := (⌈(2 : ℝ≥0) ^ m * s⌉₊ : ℝ≥0) / (2 : ℝ≥0) ^ m

lemma le_dyUp (m : ℕ) (s : ℝ≥0) : s ≤ dyUp m s := by
  unfold dyUp
  have hp : (0 : ℝ≥0) < (2 : ℝ≥0) ^ m := pow_pos (by norm_num) m
  rw [le_div_iff₀ hp, mul_comm]
  exact Nat.le_ceil _

lemma dyUp_le (m : ℕ) (s : ℝ≥0) : dyUp m s ≤ s + 1 / (2 : ℝ≥0) ^ m := by
  unfold dyUp
  have hp : (0 : ℝ≥0) < (2 : ℝ≥0) ^ m := pow_pos (by norm_num) m
  rw [div_le_iff₀ hp, add_mul, one_div, inv_mul_cancel₀ hp.ne', mul_comm s]
  exact (Nat.ceil_lt_add_one (by positivity)).le

lemma tendsto_dyUp (s : ℝ≥0) : Tendsto (fun m => dyUp m s) atTop (𝓝[≥] s) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => le_dyUp m s⟩
  have h1 : Tendsto (fun m : ℕ => s + 1 / (2 : ℝ≥0) ^ m) atTop (𝓝 (s + 0)) := by
    refine tendsto_const_nhds.add ?_
    simp only [one_div]
    have := (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ≥0)) (by norm_num))
    simpa [inv_pow] using this
  rw [add_zero] at h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun m => le_dyUp m s) (fun m => dyUp_le m s)

/-- evaluating a right-continuous, coordinatewise measurable process at a measurable random time -/
lemma measurable_eval_rc {Ω S : Type*} [MeasurableSpace Ω] [TopologicalSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S] [MeasurableSpace S] [BorelSpace S]
    (X : Ω → ℝ≥0 → S) (hc : ∀ ω t, ContinuousWithinAt (X ω) (Set.Ici t) t)
    (hm : ∀ t, Measurable fun ω => X ω t) (σ : Ω → ℝ≥0) (hσ : Measurable σ) :
    Measurable fun ω => X ω (σ ω) := by
  have happ : ∀ m : ℕ, Measurable fun ω => X ω (dyUp m (σ ω)) := by
    intro m
    have hF : Measurable fun p : Ω × ℕ => X p.1 ((p.2 : ℝ≥0) / (2 : ℝ≥0) ^ m) :=
      measurable_from_prod_countable_left fun n => hm ((n : ℝ≥0) / (2 : ℝ≥0) ^ m)
    have hn : Measurable fun ω => ⌈(2 : ℝ≥0) ^ m * σ ω⌉₊ :=
      Nat.measurable_ceil.comp (measurable_const.mul hσ)
    exact hF.comp (measurable_id.prodMk hn)
  refine measurable_of_tendsto_metrizable happ ?_
  rw [tendsto_pi_nhds]
  intro ω
  exact (hc ω (σ ω)).tendsto.comp (tendsto_dyUp (σ ω))

open KurtzProtter91.Integrals (IsCadlag)

lemma isCadlag_shift {E : Type*} [TopologicalSpace E] (x : ℝ≥0 → E) (hx : IsCadlag x) (c : ℝ≥0) :
    IsCadlag fun t => x (c + t) := by
  refine ⟨fun t => ?_, fun t ht => ?_⟩
  · have hcont : ContinuousWithinAt (fun s : ℝ≥0 => c + s) (Set.Ici t) t :=
      (continuous_const.add continuous_id).continuousWithinAt
    exact (hx.1 (c + t)).comp hcont (fun s hs => by simpa using hs)
  · obtain ⟨a, ha⟩ := hx.2 (c + t) (by positivity)
    refine ⟨a, ha.comp ?_⟩
    have hcont : Tendsto (fun s : ℝ≥0 => c + s) (𝓝 t) (𝓝 (c + t)) :=
      (continuous_const.add continuous_id).tendsto t
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hcont.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs => by simpa using hs)

lemma isCadlag_comp {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] (x : ℝ≥0 → E)
    (hx : IsCadlag x) (f : E → F) (hf : Continuous f) : IsCadlag (f ∘ x) := by
  refine ⟨fun t => (hf.continuousAt).comp_continuousWithinAt (hx.1 t), fun t ht => ?_⟩
  obtain ⟨a, ha⟩ := hx.2 t ht
  exact ⟨f a, (hf.tendsto a).comp ha⟩

lemma isCadlag_const {E : Type*} [TopologicalSpace E] (e : E) : IsCadlag fun _ : ℝ≥0 => e :=
  ⟨fun _ => continuousWithinAt_const, fun _ _ => ⟨e, tendsto_const_nhds⟩⟩

/-- exit time of a path shifted by `c`, when no exit happens before `c` -/
lemma exitTime_shift {S : Type*} (A : Set S) (x : ℝ≥0 → S ⊕ Unit) (c : ℝ≥0)
    (hc : (c : ℝ≥0∞) ≤ exitTime A x) :
    (c : ℝ≥0∞) + exitTime A (fun t => x (c + t)) = exitTime A x := by
  apply le_antisymm
  · unfold exitTime
    refine le_iInf₂ fun s hs => ?_
    have hcs : (c : ℝ≥0∞) ≤ s := hc.trans (iInf₂_le s hs)
    have hcs' : c ≤ s := by exact_mod_cast hcs
    have hmem : ∃ a, a ∉ A ∧ x (c + (s - c)) = Sum.inl a := by
      rw [add_tsub_cancel_of_le hcs']; exact hs
    calc (c : ℝ≥0∞) + ⨅ (t : ℝ≥0) (_ : ∃ a, a ∉ A ∧ x (c + t) = Sum.inl a), (t : ℝ≥0∞)
        ≤ (c : ℝ≥0∞) + ((s - c : ℝ≥0) : ℝ≥0∞) := add_le_add_right (iInf₂_le (s - c) hmem) _
      _ = s := by rw [← ENNReal.coe_add, add_tsub_cancel_of_le hcs']
  · unfold exitTime
    rw [ENNReal.add_iInf]
    refine le_iInf fun t => ?_
    rw [ENNReal.add_iInf]
    refine le_iInf fun ht => ?_
    rw [← ENNReal.coe_add]
    exact iInf₂_le (c + t) ht

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- the path of `X` in `S̃` -/
def pathOf (ω : Ω) : Path S :=
  ⟨fun t => Sum.inl (M.X ω t), isCadlag_comp _ (M.cadlag ω) Sum.inl continuous_inl⟩

lemma measurable_pathOf : Measurable (pathOf M) := by
  refine Measurable.subtype_mk ?_
  exact measurable_pi_lambda _ fun t => measurable_inl.comp (M.measurable_X t)

lemma measurable_Γ : Measurable M.Γ :=
  M.exit_measurable.comp (measurable_pathOf M)

/-- the event `{T(0) ⩽ Γ}` -/
def S0 : Set Ω := {ω | M.T 0 ω ≤ M.Γ ω}

lemma measurableSet_S0 : MeasurableSet (S0 M) :=
  measurableSet_le (M.measurable_T 0) (measurable_Γ M)

lemma T0_ne_top {ω : Ω} (hω : ω ∈ S0 M) : M.T 0 ω ≠ ⊤ := by
  intro h
  have h1 := M.T_top 0 ω h
  have h2 : M.T 0 ω ≤ M.Γ ω := hω
  rw [h] at h2
  exact absurd (top_le_iff.1 h2) (ne_of_lt (by simpa [Model.Γ] using h1))

lemma T0_le_T (n : ℕ) (ω : Ω) : M.T 0 ω ≤ M.T n ω := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (M.T_mono n ω)

/-- the start of the first full cycle as an `ℝ≥0` time -/
noncomputable def t0 (ω : S0 M) : ℝ≥0 := (M.T 0 ω.1).toNNReal

lemma coe_t0 (ω : S0 M) : ((t0 M ω : ℝ≥0) : ℝ≥0∞) = M.T 0 ω.1 :=
  ENNReal.coe_toNNReal (T0_ne_top M ω.2)

lemma measurable_t0 : Measurable (t0 M) :=
  ((M.measurable_T 0).comp measurable_subtype_coe).ennreal_toNNReal

/-- shifted process `X'(t) = X(T(0) + t)` -/
noncomputable def Xs (ω : S0 M) (t : ℝ≥0) : S := M.X ω.1 (t0 M ω + t)

/-- shifted regeneration times `T'(n) = T(n) − T(0)` -/
noncomputable def Ts (n : ℕ) (ω : S0 M) : ℝ≥0∞ := M.T n ω.1 - M.T 0 ω.1

lemma Γs_eq (ω : S0 M) :
    (M.T 0 ω.1) + exitTime A (fun t => Sum.inl (Xs M ω t)) = M.Γ ω.1 := by
  rw [← coe_t0 M ω]
  exact exitTime_shift A (fun t => Sum.inl (M.X ω.1 t)) (t0 M ω) (by rw [coe_t0 M ω]; exact ω.2)

lemma Γs_eq' (ω : S0 M) :
    exitTime A (fun t => Sum.inl (Xs M ω t)) = M.Γ ω.1 - M.T 0 ω.1 := by
  rw [← Γs_eq M ω, ENNReal.add_sub_cancel_left (T0_ne_top M ω.2)]

lemma Ts_zero (ω : S0 M) : Ts M 0 ω = 0 := by simp [Ts]

lemma T_ne_top_of_Ts {n : ℕ} {ω : S0 M} (h : Ts M n ω ≠ ⊤) : M.T n ω.1 ≠ ⊤ := by
  intro hT
  apply h
  simp only [Ts, hT]
  exact ENNReal.top_sub (T0_ne_top M ω.2)

lemma Ts_ne_top_of_T {n : ℕ} {ω : S0 M} (h : M.T n ω.1 ≠ ⊤) : Ts M n ω ≠ ⊤ :=
  ne_top_of_le_ne_top h tsub_le_self

lemma sub_lt_sub_iff' {a b c : ℝ≥0∞} (hc : c ≠ ⊤) (ha : c ≤ a) : a - c < b - c ↔ a < b :=
  by
  constructor
  · intro h
    by_contra hb
    exact absurd h (not_lt.2 (tsub_le_tsub_right (not_lt.1 hb) _))
  · intro h
    have hb : c ≤ b := ha.trans h.le
    rw [← ENNReal.add_lt_add_iff_right hc, tsub_add_cancel_of_le ha, tsub_add_cancel_of_le hb]
    exact h

lemma cycleOf_shift (n : ℕ) (ω : S0 M) :
    cycleOf (Xs M) (Ts M) (n + 1) ω = cycleOf M.X M.T (n + 1) ω.1 := by
  funext t
  have hc := T0_ne_top M ω.2
  have ha : M.T 0 ω.1 ≤ M.T n ω.1 := T0_le_T M n ω.1
  have hpt : prevTime (Ts M) (n + 1) ω = M.T n ω.1 - M.T 0 ω.1 := by simp [prevTime, Ts]
  have hp : prevTime M.T (n + 1) ω.1 = M.T n ω.1 := by simp [prevTime]
  have hre : M.T n ω.1 - M.T 0 ω.1 + (t : ℝ≥0∞) = M.T n ω.1 + t - M.T 0 ω.1 :=
    ENNReal.sub_add_eq_add_sub ha hc
  have hiff : M.T n ω.1 - M.T 0 ω.1 + (t : ℝ≥0∞) < Ts M (n + 1) ω ↔
      M.T n ω.1 + t < M.T (n + 1) ω.1 := by
    rw [hre, Ts]
    exact sub_lt_sub_iff' hc (ha.trans le_self_add)
  unfold cycleOf
  rw [hpt, hp]
  by_cases hlt : M.T n ω.1 + t < M.T (n + 1) ω.1
  · rw [if_pos (hiff.2 hlt), if_pos hlt]
    congr 1
    unfold Xs
    congr 1
    have hfin : M.T n ω.1 + (t : ℝ≥0∞) ≠ ⊤ := ne_top_of_lt hlt
    apply ENNReal.coe_injective
    rw [ENNReal.coe_add, coe_t0, ENNReal.coe_toNNReal (by rw [hre]; exact ne_top_of_le_ne_top hfin tsub_le_self),
      ENNReal.coe_toNNReal hfin, hre]
    exact add_tsub_cancel_of_le (ha.trans le_self_add)
  · rw [if_neg (fun h => hlt (hiff.1 h)), if_neg hlt]

/-- shifted cycles: `W'₀ = Δ`, `W'ₙ = Wₙ` for `n ⩾ 1` -/
noncomputable def Ws : ℕ → S0 M → Path S
  | 0, _ => ⟨fun _ => Sum.inr (), isCadlag_const _⟩
  | n + 1, ω => M.W (n + 1) ω.1

section ExitDecomp
variable {Ω' : Type*} [MeasurableSpace Ω'] (N : Model S A Ω')

/-- `Ψ = inf_j (T(j-1) + γ_j)`: the first exit read off the cycles -/
noncomputable def Ψ (ω : Ω') : ℝ≥0∞ := ⨅ j, (N.Tm j ω + N.γ j ω)

lemma Γ_le_Tm_add_γ (ω : Ω') (j : ℕ) : N.Γ ω ≤ N.Tm j ω + N.γ j ω := by
  unfold Model.γ exitTime
  rw [ENNReal.add_iInf]
  refine le_iInf fun s => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hs => ?_
  rw [N.W_eq] at hs
  unfold cycleOf at hs
  split_ifs at hs with hlt
  · obtain ⟨a, ha, hxa⟩ := hs
    have hfin : prevTime N.T j ω + (s : ℝ≥0∞) ≠ ⊤ := ne_top_of_lt hlt
    have hx : N.X ω (prevTime N.T j ω + (s : ℝ≥0∞)).toNNReal = a := Sum.inl_injective hxa
    unfold Model.Γ exitTime
    refine (iInf₂_le (prevTime N.T j ω + (s : ℝ≥0∞)).toNNReal ⟨a, ha, congrArg Sum.inl hx⟩).trans ?_
    rw [ENNReal.coe_toNNReal hfin]
    rfl
  · obtain ⟨a, _, hxa⟩ := hs
    exact absurd hxa (by simp)

lemma Γ_le_Ψ (ω : Ω') : N.Γ ω ≤ Ψ N ω := le_iInf fun j => Γ_le_Tm_add_γ N ω j

lemma Ψ_le_Γ (ω : Ω') (n : ℕ) (h : N.Γ ω < N.T n ω) : Ψ N ω ≤ N.Γ ω := by
  by_contra hlt
  push_neg at hlt
  have hb : N.Γ ω < min (Ψ N ω) (N.T n ω) := lt_min hlt h
  unfold Model.Γ exitTime at hb
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 hb
  obtain ⟨hex, ht⟩ := iInf_lt_iff.1 ht
  have htn : (t : ℝ≥0∞) < N.T n ω := lt_of_lt_of_le ht (min_le_right _ _)
  have hex' : ∃ m, (t : ℝ≥0∞) < N.T m ω := ⟨n, htn⟩
  classical
  set j := Nat.find hex' with hj
  have hjt : (t : ℝ≥0∞) < N.T j ω := Nat.find_spec hex'
  have hTm : N.Tm j ω ≤ t := by
    unfold Model.Tm prevTime
    split_ifs with h0
    · positivity
    · have := Nat.find_min hex' (show j - 1 < j by omega)
      exact not_lt.1 this
  have hTmfin : N.Tm j ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hTm
  set s' : ℝ≥0 := t - (N.Tm j ω).toNNReal with hs'
  have hsum : N.Tm j ω + (s' : ℝ≥0∞) = t := by
    rw [hs', ENNReal.coe_sub, ENNReal.coe_toNNReal hTmfin]
    exact add_tsub_cancel_of_le hTm
  have hγ : N.γ j ω ≤ s' := by
    unfold Model.γ exitTime
    refine iInf₂_le s' ?_
    rw [N.W_eq]
    unfold cycleOf
    have hc : prevTime N.T j ω + (s' : ℝ≥0∞) < N.T j ω := by
      change N.Tm j ω + (s' : ℝ≥0∞) < N.T j ω
      rw [hsum]; exact hjt
    rw [if_pos hc]
    obtain ⟨a, ha, hxa⟩ := hex
    refine ⟨a, ha, ?_⟩
    change Sum.inl (N.X ω (N.Tm j ω + (s' : ℝ≥0∞)).toNNReal) = Sum.inl a
    rw [hsum, ENNReal.toNNReal_coe]
    exact hxa
  have h1 : Ψ N ω ≤ N.Tm j ω + N.γ j ω := iInf_le _ j
  have h2 : N.Tm j ω + N.γ j ω ≤ t := by
    calc N.Tm j ω + N.γ j ω ≤ N.Tm j ω + s' := add_le_add_right hγ _
      _ = t := hsum
  have h3 : (t : ℝ≥0∞) < Ψ N ω := lt_of_lt_of_le ht (min_le_left _ _)
  exact absurd (h1.trans h2) (not_le.2 h3)

lemma lt_Γ_iff_lt_Ψ (ω : Ω') (n : ℕ) (x : ℝ≥0∞) (hx : x < N.T n ω) :
    x < N.Γ ω ↔ x < Ψ N ω := by
  constructor
  · intro h; exact lt_of_lt_of_le h (Γ_le_Ψ N ω)
  · intro h
    by_contra hΓ
    push_neg at hΓ
    exact absurd (lt_of_lt_of_le h ((Ψ_le_Γ N ω n (lt_of_le_of_lt hΓ hx)).trans hΓ)) (lt_irrefl _)

end ExitDecomp

section CycleFun

open Classical in
/-- the length of a cycle path: the first time it is `Δ` (read on rational times) -/
noncomputable def len (p : Path S) : ℝ≥0∞ :=
  ⨅ q : ℚ, if p.1 (Real.toNNReal q) = Sum.inr () then ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) else ⊤

lemma measurable_val_path : Measurable fun p : Path S => p.1 :=
  measurable_iff_comap_le.2 le_rfl

lemma measurable_eval_path (t : ℝ≥0) : Measurable fun p : Path S => p.1 t :=
  (measurable_pi_apply t).comp measurable_val_path

lemma measurable_len : Measurable (len (S := S)) := by
  refine Measurable.iInf fun q => Measurable.ite ?_ measurable_const measurable_const
  have h : {p : Path S | p.1 (Real.toNNReal q) = Sum.inr ()} =
      (fun p : Path S => p.1 (Real.toNNReal q)) ⁻¹' Set.range Sum.inr := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
    constructor
    · intro h; exact ⟨(), h.symm⟩
    · rintro ⟨u, hu⟩; rw [← hu]
  rw [h]
  exact (measurable_eval_path _) measurableSet_range_inr

lemma Tm_le_T {Ω' : Type*} [MeasurableSpace Ω'] (N : Model S A Ω') (n : ℕ) (ω : Ω') :
    N.Tm n ω ≤ N.T n ω := by
  unfold Model.Tm prevTime
  split_ifs with h
  · positivity
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simpa using N.T_mono m ω

lemma len_W {Ω' : Type*} [MeasurableSpace Ω'] (N : Model S A Ω') (n : ℕ) (ω : Ω') :
    len (N.W n ω) = N.τ n ω := by
  have hW : ∀ s : ℝ≥0, (N.W n ω).1 s = Sum.inr () ↔ N.T n ω ≤ N.Tm n ω + s := by
    intro s
    rw [N.W_eq]
    unfold cycleOf
    change (if N.Tm n ω + (s : ℝ≥0∞) < N.T n ω then _ else _) = _ ↔ _
    split_ifs with h
    · simp only [reduceCtorEq, false_iff, not_le]; exact h
    · simp only [true_iff]; exact not_lt.1 h
  unfold len
  simp_rw [hW]
  by_cases hTm : N.Tm n ω = ⊤
  · have hT : N.T n ω = ⊤ := top_le_iff.1 (hTm ▸ Tm_le_T N n ω)
    have hτ : N.τ n ω = 0 := by simp [Model.τ, hT, hTm]
    rw [hτ]
    refine le_antisymm ((iInf_le _ (0 : ℚ)).trans ?_) bot_le
    simp [hTm]
  · have hiff : ∀ q : ℚ, N.T n ω ≤ N.Tm n ω + ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) ↔
        N.τ n ω ≤ ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) := by
      intro q
      unfold Model.τ
      rw [tsub_le_iff_left]
    simp_rw [hiff]
    apply le_antisymm
    · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
      obtain ⟨q, _, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hc
      refine (iInf_le _ q).trans ?_
      rw [if_pos hq1.le]
      exact hq2.le
    · refine le_iInf fun q => ?_
      split_ifs with h
      · exact h
      · exact le_top

/-- partial sums of cycle lengths: `T(n) − T(0)` read off the cycles `W₁, W₂, …` -/
noncomputable def Tx (x : ℕ → Path S) (n : ℕ) : ℝ≥0∞ := ∑ i ∈ Finset.range n, len (x i)

/-- first exit read off the cycles `W₁, W₂, …` -/
noncomputable def Ψx (x : ℕ → Path S) : ℝ≥0∞ := ⨅ i, (Tx x i + exitTime A (x i).1)

/-- straddling index read off the cycles -/
noncomputable def stradx (u : ℝ) (x : ℕ → Path S) : ℕ := sInf {n : ℕ | ENNReal.ofReal u < Tx x n}

lemma measurable_Tx (n : ℕ) : Measurable fun x : ℕ → Path S => Tx x n :=
  Finset.measurable_sum _ fun i _ => measurable_len.comp (measurable_pi_apply i)

lemma measurable_Ψx (hγ : Measurable fun x : Path S => exitTime A x.1) :
    Measurable fun x : ℕ → Path S => Ψx (A := A) x :=
  Measurable.iInf fun i => (measurable_Tx i).add (hγ.comp (measurable_pi_apply i))

lemma Tx_mono (x : ℕ → Path S) {m n : ℕ} (h : m ≤ n) : Tx x m ≤ Tx x n :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

end CycleFun

section EventSet

lemma stradx_eq_succ_iff (u : ℝ) (x : ℕ → Path S) (n : ℕ) :
    stradx u x = n + 1 ↔ ENNReal.ofReal u < Tx x (n + 1) ∧ Tx x n ≤ ENNReal.ofReal u := by
  unfold stradx
  constructor
  · intro h
    have hne : {m : ℕ | ENNReal.ofReal u < Tx x m}.Nonempty := by
      by_contra he
      rw [Set.not_nonempty_iff_eq_empty] at he
      rw [he, Nat.sInf_empty] at h
      omega
    have h1 := Nat.sInf_mem hne
    rw [h] at h1
    refine ⟨h1, ?_⟩
    have h2 := Nat.notMem_of_lt_sInf (show n < sInf {m : ℕ | ENNReal.ofReal u < Tx x m} by omega)
    exact not_lt.1 h2
  · rintro ⟨h1, h2⟩
    apply le_antisymm (Nat.sInf_le h1)
    refine le_csInf ⟨_, h1⟩ fun m hm => ?_
    by_contra hmn
    have : Tx x m ≤ Tx x n := Tx_mono x (by omega)
    exact absurd hm (not_lt.2 (this.trans h2))

/-- the event of Theorem 2 (non-delayed), read off `(u, W₁, W₂, …)` -/
def Cset (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) : Set (ℝ × (ℕ → Path S)) :=
  {p | k < stradx p.1 p.2 ∧
    ((fun i : Fin (2 * k + 1) => p.2 (stradx p.1 p.2 - k + i - 1)),
      p.1 - (Tx p.2 (stradx p.1 p.2 - 1)).toReal) ∈ B ∧ ENNReal.ofReal p.1 < Ψx (A := A) p.2}

lemma Cset_eq (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) :
    Cset (A := A) k B = ⋃ n : ℕ,
      ({p : ℝ × (ℕ → Path S) | ENNReal.ofReal p.1 < Tx p.2 (n + 1) ∧ Tx p.2 n ≤ ENNReal.ofReal p.1} ∩
        {p | k < n + 1 ∧ ((fun i : Fin (2 * k + 1) => p.2 (n + 1 - k + i - 1)),
          p.1 - (Tx p.2 n).toReal) ∈ B ∧ ENNReal.ofReal p.1 < Ψx (A := A) p.2}) := by
  ext p
  simp only [Cset, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨hk, hB, hΨ⟩
    obtain ⟨n, hn⟩ : ∃ n, stradx p.1 p.2 = n + 1 := ⟨stradx p.1 p.2 - 1, by omega⟩
    refine ⟨n, (stradx_eq_succ_iff _ _ _).1 hn, ?_⟩
    rw [hn] at hk hB
    exact ⟨hk, by simpa using hB, hΨ⟩
  · rintro ⟨n, hn, hk, hB, hΨ⟩
    have hs := (stradx_eq_succ_iff _ _ _).2 hn
    rw [hs]
    exact ⟨hk, by simpa using hB, hΨ⟩

lemma measurableSet_Cset (hγ : Measurable fun x : Path S => exitTime A x.1) (k : ℕ)
    (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (Cset (A := A) k B) := by
  rw [Cset_eq]
  refine MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ ?_
  · exact (measurableSet_lt (measurable_fst.ennreal_ofReal) ((measurable_Tx (n + 1)).comp measurable_snd)).inter
      (measurableSet_le ((measurable_Tx n).comp measurable_snd) measurable_fst.ennreal_ofReal)
  · refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.inter ?_ ?_)
    · have hg : Measurable fun p : ℝ × (ℕ → Path S) =>
          ((fun i : Fin (2 * k + 1) => p.2 (n + 1 - k + i - 1)), p.1 - (Tx p.2 n).toReal) :=
        (measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_snd).prodMk
          (measurable_fst.sub ((measurable_Tx n).comp measurable_snd).ennreal_toReal)
      exact hg hB
    · exact measurableSet_lt measurable_fst.ennreal_ofReal ((measurable_Ψx hγ).comp measurable_snd)

variable {Ω' : Type*} [MeasurableSpace Ω'] (N : Model S A Ω')

/-- the cycles `W₁, W₂, …` -/
def cyc (ω : Ω') : ℕ → Path S := fun i => N.W (1 + i) ω

lemma T_eq_Tx (ω : Ω') (h0 : N.T 0 ω = 0) (n : ℕ) : N.T n ω = Tx (cyc N ω) n := by
  induction n with
  | zero => simp [Tx, h0]
  | succ n ih =>
    rw [Tx, Finset.sum_range_succ, ← Tx, ← ih, cyc, len_W]
    have hτ : N.τ (1 + n) ω = N.T (n + 1) ω - N.T n ω := by
      simp [Model.τ, Model.Tm, prevTime, add_comm 1 n]
    rw [hτ]
    by_cases hT : N.T n ω = ⊤
    · have h1 : N.T (n + 1) ω = ⊤ := top_le_iff.1 (hT ▸ N.T_mono n ω)
      rw [hT, h1]; simp
    · exact (add_tsub_cancel_of_le (N.T_mono n ω)).symm

lemma γ0_top (ω : Ω') (h0 : N.T 0 ω = 0) : N.γ 0 ω = ⊤ := by
  unfold Model.γ exitTime
  refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun ht => ?_
  exfalso
  obtain ⟨a, _, hxa⟩ := ht
  rw [N.W_eq] at hxa
  unfold cycleOf at hxa
  rw [if_neg (by simp [prevTime, h0])] at hxa
  exact absurd hxa (by simp)

lemma Ψ_eq_Ψx (ω : Ω') (h0 : N.T 0 ω = 0) : Ψ N ω = Ψx (A := A) (cyc N ω) := by
  unfold Ψ Ψx
  apply le_antisymm
  · refine le_iInf fun i => (iInf_le _ (1 + i)).trans (le_of_eq ?_)
    rw [← T_eq_Tx N ω h0]
    simp [Model.Tm, prevTime, Model.γ, cyc]
  · refine le_iInf fun j => ?_
    cases j with
    | zero => simp [γ0_top N ω h0]
    | succ i =>
      refine (iInf_le _ i).trans (le_of_eq ?_)
      rw [← T_eq_Tx N ω h0]
      simp [Model.Tm, prevTime, Model.γ, cyc, add_comm 1 i]

lemma strad_eq_stradx (ω : Ω') (h0 : N.T 0 ω = 0) (u : ℝ) : N.strad u ω = stradx u (cyc N ω) := by
  unfold Model.strad stradx
  simp_rw [T_eq_Tx N ω h0]

lemma event_iff_Cset (ω : Ω') (h0 : N.T 0 ω = 0) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ))
    (u : ℝ) :
    (k < N.strad u ω ∧ (N.win k u ω, N.age u ω) ∈ B ∧ ENNReal.ofReal u < N.Γ ω) ↔
      (u, cyc N ω) ∈ Cset (A := A) k B := by
  unfold Model.win Model.age
  rw [strad_eq_stradx N ω h0]
  simp only [Cset, Set.mem_setOf_eq]
  set n := stradx u (cyc N ω) with hn
  constructor
  · rintro ⟨hk, hB, hΓ⟩
    have hne : {m : ℕ | ENNReal.ofReal u < Tx (cyc N ω) m}.Nonempty := by
      by_contra he
      rw [Set.not_nonempty_iff_eq_empty] at he
      have : n = 0 := by rw [hn, stradx, he, Nat.sInf_empty]
      omega
    have hmem : ENNReal.ofReal u < N.T n ω := by
      rw [T_eq_Tx N ω h0]; exact Nat.sInf_mem hne
    refine ⟨hk, ?_, ?_⟩
    · have hW : (fun i : Fin (2 * k + 1) => N.W (n - k + i) ω) =
          fun i : Fin (2 * k + 1) => cyc N ω (n - k + i - 1) := by
        funext i; simp only [cyc]; congr 1; omega
      have hT : N.Tm n ω = Tx (cyc N ω) (n - 1) := by
        rw [← T_eq_Tx N ω h0]; simp [Model.Tm, prevTime, show n ≠ 0 by omega]
      rw [← hW, ← hT]; exact hB
    · rw [← Ψ_eq_Ψx N ω h0]; exact (lt_Γ_iff_lt_Ψ N ω n _ hmem).1 hΓ
  · rintro ⟨hk, hB, hΨ⟩
    have hne : {m : ℕ | ENNReal.ofReal u < Tx (cyc N ω) m}.Nonempty := by
      by_contra he
      rw [Set.not_nonempty_iff_eq_empty] at he
      have : n = 0 := by rw [hn, stradx, he, Nat.sInf_empty]
      omega
    have hmem : ENNReal.ofReal u < N.T n ω := by
      rw [T_eq_Tx N ω h0]; exact Nat.sInf_mem hne
    refine ⟨hk, ?_, ?_⟩
    · have hW : (fun i : Fin (2 * k + 1) => N.W (n - k + i) ω) =
          fun i : Fin (2 * k + 1) => cyc N ω (n - k + i - 1) := by
        funext i; simp only [cyc]; congr 1; omega
      have hT : N.Tm n ω = Tx (cyc N ω) (n - 1) := by
        rw [← T_eq_Tx N ω h0]; simp [Model.Tm, prevTime, show n ≠ 0 by omega]
      rw [hW, hT]; exact hB
    · rw [← Ψ_eq_Ψx N ω h0] at hΨ; exact (lt_Γ_iff_lt_Ψ N ω n _ hmem).2 hΨ

end EventSet

end TabooRegen.DelayShift

namespace TabooRegen.DelayShift
open TabooRegen TabooRegen.Model KurtzProtter91.Integrals

variable {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
  {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- the non-delayed version: `Ω' = {T(0) ⩽ Γ}` with `P' = Q`, time shifted by `T(0)` -/
noncomputable def shiftModel (hP : M.P (S0 M) ≠ 0) : Model S A (S0 M) where
  P := M.Q.comap Subtype.val
  isProb := by
    have := M.isProb
    constructor
    rw [comap_subtype_coe_apply (measurableSet_S0 M), Set.image_univ, Subtype.range_coe]
    exact ProbabilityTheory.cond_apply_self hP (measure_ne_top _ _)
  X := Xs M
  cadlag := fun ω => isCadlag_shift _ (M.cadlag ω.1) _
  measurable_X := fun t => by
    have h := measurable_eval_rc (fun ω : S0 M => M.X ω.1) (fun ω s => (M.cadlag ω.1).1 s)
      (fun s => (M.measurable_X s).comp measurable_subtype_coe) (fun ω => t0 M ω + t)
      ((measurable_t0 M).add measurable_const)
    exact h
  exit_measurable := M.exit_measurable
  T := Ts M
  measurable_T := fun n =>
    ((M.measurable_T n).comp measurable_subtype_coe).sub ((M.measurable_T 0).comp measurable_subtype_coe)
  T_mono := fun n ω => tsub_le_tsub_right (M.T_mono n ω.1) _
  T_strict := fun n ω h => by
    have hT := T_ne_top_of_Ts M h.ne
    exact (sub_lt_sub_iff' (T0_ne_top M ω.2) (T0_le_T M n ω.1)).2 (M.T_strict n ω.1 hT.lt_top)
  taboo := fun n ω h => by
    rw [Γs_eq' M ω] at h
    have hlt : M.Γ ω.1 < M.T n ω.1 := by
      by_contra hge
      exact absurd h (not_lt.2 (tsub_le_tsub_right (not_lt.1 hge) _))
    have hT := M.taboo n ω.1 hlt
    simp only [Ts, hT]
    exact ENNReal.top_sub (T0_ne_top M ω.2)
  T_top := fun n ω h => by
    rw [Γs_eq' M ω]
    have hT : M.T n ω.1 = ⊤ := by
      by_contra hne; exact Ts_ne_top_of_T M hne h
    exact lt_of_le_of_lt tsub_le_self (M.T_top n ω.1 hT)
  W := Ws M
  measurable_W := fun n => by
    cases n with
    | zero => exact measurable_const
    | succ n => exact (M.measurable_W (n + 1)).comp measurable_subtype_coe
  W_eq := fun n ω => by
    cases n with
    | zero =>
      funext t
      simp [Ws, cycleOf, prevTime, Ts]
    | succ n =>
      rw [cycleOf_shift M n ω]
      exact M.W_eq (n + 1) ω.1

variable (hP : M.P (S0 M) ≠ 0)

lemma Ws_of_pos (n : ℕ) (hn : 1 ≤ n) (ω : S0 M) : Ws M n ω = M.W n ω.1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

lemma sh_T (n : ℕ) (ω : S0 M) : (shiftModel M hP).T n ω = M.T n ω.1 - M.T 0 ω.1 := rfl

lemma sh_W (n : ℕ) (hn : 1 ≤ n) (ω : S0 M) : (shiftModel M hP).W n ω = M.W n ω.1 :=
  Ws_of_pos M n hn ω

lemma sh_Γ (ω : S0 M) : (shiftModel M hP).Γ ω = M.Γ ω.1 - M.T 0 ω.1 := Γs_eq' M ω

lemma sh_T0 (ω : S0 M) : (shiftModel M hP).T 0 ω = 0 := Ts_zero M ω

lemma sh_γ (n : ℕ) (hn : 1 ≤ n) (ω : S0 M) : (shiftModel M hP).γ n ω = M.γ n ω.1 := by
  simp only [Model.γ, sh_W M hP n hn ω]

lemma sh_τ (n : ℕ) (hn : 1 ≤ n) (ω : S0 M) : (shiftModel M hP).τ n ω = M.τ n ω.1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Model.τ, Model.Tm, prevTime, sh_T, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  have hc := T0_ne_top M ω.2
  have ha : M.T 0 ω.1 ≤ M.T m ω.1 := T0_le_T M m ω.1
  have hb : M.T m ω.1 ≤ M.T (m + 1) ω.1 := M.T_mono m ω.1
  by_cases hm : M.T m ω.1 = ⊤
  · have h1 : M.T (m + 1) ω.1 = ⊤ := top_le_iff.1 (hm ▸ hb)
    rw [hm, h1]; simp
  · by_cases h1 : M.T (m + 1) ω.1 = ⊤
    · rw [h1, ENNReal.top_sub hc, ENNReal.top_sub (ENNReal.sub_ne_top hm), ENNReal.top_sub hm]
    · rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.sub_ne_top (ENNReal.sub_ne_top h1))
        (ENNReal.sub_ne_top h1)]
      rw [ENNReal.toReal_sub_of_le (tsub_le_tsub_right hb _) (ENNReal.sub_ne_top h1),
        ENNReal.toReal_sub_of_le ha hm, ENNReal.toReal_sub_of_le (ha.trans hb) h1,
        ENNReal.toReal_sub_of_le hb h1]
      ring

lemma sub_le_sub_iff'' {a b c : ℝ≥0∞} (hc : c ≠ ⊤) (ha : c ≤ a) (hb : c ≤ b) :
    a - c ≤ b - c ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    exact absurd h (not_le.2 ((sub_lt_sub_iff' hc hb).2 (not_le.1 hab)))
  · intro h; exact tsub_le_tsub_right h _

lemma sh_T_le_Γ (n : ℕ) (ω : S0 M) :
    (shiftModel M hP).T n ω ≤ (shiftModel M hP).Γ ω ↔ M.T n ω.1 ≤ M.Γ ω.1 := by
  rw [sh_T, sh_Γ]
  exact sub_le_sub_iff'' (T0_ne_top M ω.2) (T0_le_T M n ω.1) ω.2

lemma Q_restrict_S0 : M.Q.restrict (S0 M) = M.Q := by
  unfold Model.Q ProbabilityTheory.cond
  rw [Measure.restrict_smul, Measure.restrict_restrict (measurableSet_S0 M),
    show S0 M ∩ {ω | M.T 0 ω ≤ M.Γ ω} = S0 M from Set.inter_self _]
  rfl

lemma sh_Q : (shiftModel M hP).Q = (shiftModel M hP).P := by
  have := (shiftModel M hP).isProb
  unfold Model.Q
  have h : {ω | (shiftModel M hP).T 0 ω ≤ (shiftModel M hP).Γ ω} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, sh_T0]
    positivity
  rw [h, ProbabilityTheory.cond_univ]

lemma sh_lintegral (f : Ω → ℝ≥0∞) :
    ∫⁻ ω, f ω.1 ∂(shiftModel M hP).Q = ∫⁻ ω, f ω ∂M.Q := by
  rw [sh_Q]
  change ∫⁻ ω : S0 M, f ω ∂(M.Q.comap Subtype.val) = _
  rw [lintegral_subtype_comap (measurableSet_S0 M), Q_restrict_S0]

lemma sh_measure (E : Set Ω) :
    (shiftModel M hP).Q (Subtype.val ⁻¹' E) = M.Q E := by
  rw [sh_Q]
  change M.Q.comap Subtype.val (Subtype.val ⁻¹' E) = _
  rw [comap_subtype_coe_apply (measurableSet_S0 M), Subtype.image_preimage_coe]
  conv_rhs => rw [← Q_restrict_S0 M]
  rw [Measure.restrict_apply' (measurableSet_S0 M), Set.inter_comm]

lemma sh_setLIntegral (E : Set Ω) (hE : MeasurableSet E) (f : Ω → ℝ≥0∞) :
    ∫⁻ ω in Subtype.val ⁻¹' E, f ω.1 ∂(shiftModel M hP).Q = ∫⁻ ω in E, f ω ∂M.Q := by
  rw [← lintegral_indicator (hE.preimage measurable_subtype_coe), ← lintegral_indicator hE,
    ← sh_lintegral M hP]
  rfl

lemma measurable_γ' {Ω' : Type*} [MeasurableSpace Ω'] (N : Model S A Ω') (n : ℕ) :
    Measurable (N.γ n) :=
  N.exit_measurable.comp (N.measurable_W n)

lemma measurableSet_NoExit' {Ω' : Type*} [MeasurableSpace Ω'] (N : Model S A Ω') (n : ℕ) :
    MeasurableSet (N.NoExit n) :=
  measurableSet_eq_fun (measurable_γ' N n) measurable_const

lemma measurable_tau_toReal {Ω' : Type*} [MeasurableSpace Ω'] (N : Model S A Ω') (n : ℕ) :
    Measurable fun ω => (N.τ n ω).toReal := by
  have h : (fun ω => (N.τ n ω).toReal) = fun ω => (N.T n ω - prevTime N.T n ω).toReal := rfl
  rw [h]
  refine ((N.measurable_T n).sub ?_).ennreal_toReal
  unfold prevTime
  split_ifs
  · exact measurable_const
  · exact N.measurable_T _

lemma sh_γ1 (ω : S0 M) : (shiftModel M hP).γ 1 ω = M.γ 1 ω.1 := sh_γ M hP 1 le_rfl ω
lemma sh_τ1 (ω : S0 M) : (shiftModel M hP).τ 1 ω = M.τ 1 ω.1 := sh_τ M hP 1 le_rfl ω

lemma sh_NoExit1 : (shiftModel M hP).NoExit 1 = Subtype.val ⁻¹' M.NoExit 1 := by
  ext ω; simp only [Model.NoExit, Set.mem_setOf_eq, Set.mem_preimage, sh_γ1]

lemma sh_cycleMGF (θ : ℝ) : (shiftModel M hP).cycleMGF θ = M.cycleMGF θ := by
  simp only [Model.cycleMGF, sh_NoExit1, sh_τ1]
  exact sh_setLIntegral M hP _ (measurableSet_NoExit' M 1)
    (fun ω => ENNReal.ofReal (Real.exp (θ * (M.τ 1 ω).toReal)))

lemma sh_lamInv (a : ℝ) : (shiftModel M hP).lamInv a = M.lamInv a := by
  simp only [Model.lamInv, sh_NoExit1, sh_τ1]
  exact sh_setLIntegral M hP _ (measurableSet_NoExit' M 1)
    (fun ω => ENNReal.ofReal (M.τ 1 ω).toReal * ENNReal.ofReal (Real.exp (a * (M.τ 1 ω).toReal)))

lemma sh_rate (a : ℝ) : (shiftModel M hP).rate a = M.rate a := by
  simp only [Model.rate, sh_lamInv]

lemma sh_G : (shiftModel M hP).G = M.G := by
  ext s hs
  rw [Model.G, Model.G, Measure.map_apply (measurable_tau_toReal _ 1) hs,
    Measure.map_apply (measurable_tau_toReal _ 1) hs,
    Measure.restrict_apply ((measurable_tau_toReal _ 1) hs),
    Measure.restrict_apply ((measurable_tau_toReal _ 1) hs), sh_NoExit1]
  rw [← sh_measure M hP]
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, sh_τ1]

lemma sh_A4set (t : ℝ) : (shiftModel M hP).Q {ω | ENNReal.ofReal t <
    min ((shiftModel M hP).γ 1 ω) ((shiftModel M hP).τ 1 ω)} =
    M.Q {ω | ENNReal.ofReal t < min (M.γ 1 ω) (M.τ 1 ω)} := by
  rw [← sh_measure M hP]
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage, sh_γ1, sh_τ1]

lemma sh_A4With (a : ℝ) (h : ℝ → ℝ) : (shiftModel M hP).A4With a h ↔ M.A4With a h := by
  simp only [Model.A4With, sh_A4set]

lemma sh_cycleMGF_fun : (shiftModel M hP).cycleMGF = M.cycleMGF := funext (sh_cycleMGF M hP)

lemma sh_A7 : (shiftModel M hP).A7 ↔ M.A7 := by
  simp only [Model.A7, Model.κ₁, Model.κ₂, sh_cycleMGF_fun]

lemma sh_A1 (a : ℝ) : (shiftModel M hP).A1 a ↔ M.A1 a := by
  simp only [Model.A1, sh_cycleMGF]

lemma sh_A2 : (shiftModel M hP).A2 ↔ M.A2 := by
  simp only [Model.A2, sh_G]

lemma sh_A3 (a : ℝ) : (shiftModel M hP).A3 a ↔ M.A3 a := by
  simp only [Model.A3, sh_lamInv]

lemma sh_A4 (a : ℝ) : (shiftModel M hP).A4 a ↔ M.A4 a := by
  simp only [Model.A4, sh_A4With]

lemma sh_cycleWeight (a : ℝ) : (shiftModel M hP).cycleWeight a = M.cycleWeight a := by
  simp only [Model.cycleWeight, sh_γ1, sh_τ1]
  exact sh_lintegral M hP (fun ω => ∫⁻ u in {u : ℝ | 0 ≤ u ∧ ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)},
    ENNReal.ofReal (Real.exp (a * u)))

lemma T_ne_top_of_le_Γ {n : ℕ} {ω : Ω} (h : M.T n ω ≤ M.Γ ω) : M.T n ω ≠ ⊤ := by
  intro hT
  have h1 := M.T_top n ω hT
  rw [hT] at h
  exact absurd (top_le_iff.1 h) (ne_of_lt (by simpa [Model.Γ] using h1))

lemma sh_PstarNum (a : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) :
    (shiftModel M hP).PstarNum a k B = M.PstarNum a k B := by
  have hE : MeasurableSet {ω | M.T k ω ≤ M.Γ ω} :=
    measurableSet_le (M.measurable_T k) (measurable_Γ M)
  have hset : {ω | (shiftModel M hP).T k ω ≤ (shiftModel M hP).Γ ω} =
      Subtype.val ⁻¹' {ω | M.T k ω ≤ M.Γ ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, sh_T_le_Γ]
  unfold Model.PstarNum
  rw [hset, ← sh_setLIntegral M hP _ hE]
  apply setLIntegral_congr_fun (hE.preimage measurable_subtype_coe)
  intro ω hω
  have hk : M.T k ω.1 ≠ ⊤ := T_ne_top_of_le_Γ M hω
  have hT : ((shiftModel M hP).T k ω).toReal - ((shiftModel M hP).T 0 ω).toReal =
      (M.T k ω.1).toReal - (M.T 0 ω.1).toReal := by
    rw [sh_T0, sh_T, ENNReal.toReal_sub_of_le (T0_le_T M k ω.1) hk]
    simp
  have hW : (fun i : Fin (2 * k + 1) => (shiftModel M hP).W (1 + i) ω) =
      fun i : Fin (2 * k + 1) => M.W (1 + i) ω.1 :=
    funext fun i => sh_W M hP _ (by omega) ω
  simp only [hT, hW, sh_γ M hP (k + 1) (by omega), sh_τ M hP (k + 1) (by omega)]

lemma S0_inter_of_sub {E : Set Ω} (n : ℕ) (hE : E ⊆ {ω | M.T n ω ≤ M.Γ ω}) : S0 M ∩ E = E :=
  Set.inter_eq_right.2 fun ω hω => (T0_le_T M n ω).trans (hE hω)

lemma sh_hreg (hreg : M.IsWideSenseTabooRegen) : (shiftModel M hP).IsWideSenseTabooRegen := by
  intro n C hC H hH
  set f : (Fin (n + 1) → ℝ≥0∞) → (Fin (n + 1) → ℝ≥0∞) := fun x i => x i - x 0 with hf
  have hfm : Measurable f :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).sub (measurable_pi_apply 0)
  have h1 : {ω | (fun i : ℕ => (shiftModel M hP).W (n + 1 + i) ω) ∈ C} =
      Subtype.val ⁻¹' {ω | (fun i : ℕ => M.W (n + 1 + i) ω) ∈ C} := by
    ext ω
    have : (fun i : ℕ => (shiftModel M hP).W (n + 1 + i) ω) = fun i : ℕ => M.W (n + 1 + i) ω.1 :=
      funext fun i => sh_W M hP _ (by omega) ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, this]
  have h2 : {ω | (fun i : Fin (n + 1) => (shiftModel M hP).T i ω) ∈ H} =
      Subtype.val ⁻¹' {ω | (fun i : Fin (n + 1) => M.T i ω) ∈ f ⁻¹' H} := by
    ext ω
    have : (fun i : Fin (n + 1) => (shiftModel M hP).T i ω) = f (fun i : Fin (n + 1) => M.T i ω.1) := by
      funext i; simp [hf, sh_T]
    simp only [Set.mem_setOf_eq, Set.mem_preimage, this]
  have h3 : {ω | (shiftModel M hP).T n ω ≤ (shiftModel M hP).Γ ω} =
      Subtype.val ⁻¹' {ω | M.T n ω ≤ M.Γ ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, sh_T_le_Γ]
  have h4 : {ω | (fun i : ℕ => (shiftModel M hP).W (1 + i) ω) ∈ C} =
      Subtype.val ⁻¹' {ω | (fun i : ℕ => M.W (1 + i) ω) ∈ C} := by
    ext ω
    have : (fun i : ℕ => (shiftModel M hP).W (1 + i) ω) = fun i : ℕ => M.W (1 + i) ω.1 :=
      funext fun i => sh_W M hP _ (by omega) ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, this]
  rw [← sh_Q, h1, h2, h3, h4, ← Set.preimage_inter, ← Set.preimage_inter, ← Set.preimage_inter,
    sh_measure, sh_measure, sh_measure]
  have hreg' := hreg n C hC (f ⁻¹' H) (hfm hH)
  unfold Model.Q at hreg' ⊢
  have hS : MeasurableSet {ω | M.T 0 ω ≤ M.Γ ω} := measurableSet_S0 M
  have hI : ∀ E : Set Ω, E ⊆ {ω | M.T n ω ≤ M.Γ ω} → {ω | M.T 0 ω ≤ M.Γ ω} ∩ E = E :=
    fun E hE => S0_inter_of_sub M n hE
  rw [ProbabilityTheory.cond_apply hS, ProbabilityTheory.cond_apply hS,
    hI _ Set.inter_subset_right, hI _ Set.inter_subset_right, hreg', mul_assoc]

section Identity

lemma sh_cyc (ω : S0 M) : cyc (shiftModel M hP) ω = cyc M ω.1 :=
  funext fun i => sh_W M hP (1 + i) (by omega) ω

/-- on `{T(0) ⩽ Γ, T(0) ⩽ t}` the delayed event at `t` is the shifted event at `t − T(0)` -/
lemma event_shift (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (t : ℝ) (ht : 0 ≤ t)
    (ω : S0 M) (hcu : M.T 0 ω.1 ≤ ENNReal.ofReal t) :
    (k < M.strad t ω.1 ∧ (M.win k t ω.1, M.age t ω.1) ∈ B ∧ ENNReal.ofReal t < M.Γ ω.1) ↔
      (k < (shiftModel M hP).strad (t - (M.T 0 ω.1).toReal) ω ∧
        ((shiftModel M hP).win k (t - (M.T 0 ω.1).toReal) ω,
          (shiftModel M hP).age (t - (M.T 0 ω.1).toReal) ω) ∈ B ∧
        ENNReal.ofReal (t - (M.T 0 ω.1).toReal) < (shiftModel M hP).Γ ω) := by
  have hc := T0_ne_top M ω.2
  have hofu : ENNReal.ofReal (t - (M.T 0 ω.1).toReal) = ENNReal.ofReal t - M.T 0 ω.1 := by
    rw [ENNReal.ofReal_sub t ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]
  have hstrad : (shiftModel M hP).strad (t - (M.T 0 ω.1).toReal) ω = M.strad t ω.1 := by
    unfold Model.strad
    congr 1
    ext n
    simp only [Set.mem_setOf_eq, sh_T, hofu]
    exact sub_lt_sub_iff' hc hcu
  unfold Model.win Model.age
  rw [hstrad, sh_Γ, hofu, sub_lt_sub_iff' hc hcu]
  set n := M.strad t ω.1 with hn
  constructor
  · rintro ⟨hk, hB, hΓ⟩
    refine ⟨hk, ?_, hΓ⟩
    have hW : (fun i : Fin (2 * k + 1) => (shiftModel M hP).W (n - k + i) ω) =
        fun i : Fin (2 * k + 1) => M.W (n - k + i) ω.1 :=
      funext fun i => sh_W M hP _ (by omega) ω
    have hTn : M.T (n - 1) ω.1 ≤ ENNReal.ofReal t :=
      not_lt.1 (Nat.notMem_of_lt_sInf (show n - 1 < M.strad t ω.1 by omega))
    have hfin : M.T (n - 1) ω.1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTn
    have hage : t - (M.T 0 ω.1).toReal - ((shiftModel M hP).Tm n ω).toReal =
        t - (M.Tm n ω.1).toReal := by
      simp only [Model.Tm, prevTime, show n ≠ 0 by omega, if_false, sh_T]
      rw [ENNReal.toReal_sub_of_le (T0_le_T M _ _) hfin]
      ring
    rw [hW, hage]; exact hB
  · rintro ⟨hk, hB, hΓ⟩
    refine ⟨hk, ?_, hΓ⟩
    have hW : (fun i : Fin (2 * k + 1) => (shiftModel M hP).W (n - k + i) ω) =
        fun i : Fin (2 * k + 1) => M.W (n - k + i) ω.1 :=
      funext fun i => sh_W M hP _ (by omega) ω
    have hTn : M.T (n - 1) ω.1 ≤ ENNReal.ofReal t :=
      not_lt.1 (Nat.notMem_of_lt_sInf (show n - 1 < M.strad t ω.1 by omega))
    have hfin : M.T (n - 1) ω.1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTn
    have hage : t - (M.T 0 ω.1).toReal - ((shiftModel M hP).Tm n ω).toReal =
        t - (M.Tm n ω.1).toReal := by
      simp only [Model.Tm, prevTime, show n ≠ 0 by omega, if_false, sh_T]
      rw [ENNReal.toReal_sub_of_le (T0_le_T M _ _) hfin]
      ring
    rw [hW, hage] at hB; exact hB

include hP in
lemma delayed_event_iff (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (t : ℝ) (ht : 0 ≤ t)
    (ω : Ω) :
    (k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧ ENNReal.ofReal t < M.Γ ω) ↔
      (ω ∈ S0 M ∧ M.T 0 ω ≤ ENNReal.ofReal t ∧
        (t - (M.T 0 ω).toReal, cyc M ω) ∈ Cset (A := A) k B) := by
  constructor
  · intro h
    have hT0 : M.T 0 ω ≤ ENNReal.ofReal t :=
      not_lt.1 (Nat.notMem_of_lt_sInf (show 0 < M.strad t ω by omega))
    have hS : ω ∈ S0 M := hT0.trans h.2.2.le
    refine ⟨hS, hT0, ?_⟩
    have h' := (event_shift M hP k B t ht ⟨ω, hS⟩ hT0).1 h
    rw [event_iff_Cset _ _ (sh_T0 M hP _), sh_cyc] at h'
    exact h'
  · rintro ⟨hS, hT0, hC⟩
    refine (event_shift M hP k B t ht ⟨ω, hS⟩ hT0).2 ?_
    rw [event_iff_Cset _ _ (sh_T0 M hP _), sh_cyc]
    exact hC

lemma measurable_cyc {Ω' : Type*} [MeasurableSpace Ω'] (N : Model S A Ω') : Measurable (cyc N) :=
  measurable_pi_lambda _ fun i => N.measurable_W (1 + i)

lemma Q_finite : IsFiniteMeasure M.Q := by
  have := M.isProb
  unfold Model.Q
  infer_instance

lemma prod_law (hreg : M.IsWideSenseTabooRegen) :
    (M.P.restrict (S0 M)).map (fun ω => (M.T 0 ω, cyc M ω)) =
      ((M.P.restrict (S0 M)).map (M.T 0)).prod (M.Q.map (cyc M)) := by
  have := M.isProb
  have := Q_finite M
  have hg : Measurable fun ω => (M.T 0 ω, cyc M ω) := (M.measurable_T 0).prodMk (measurable_cyc M)
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hg (hs.prod ht), Measure.map_apply (M.measurable_T 0) hs,
    Measure.map_apply (measurable_cyc M) ht, Measure.restrict_apply (hg (hs.prod ht)),
    Measure.restrict_apply ((M.measurable_T 0) hs)]
  have h := hreg 0 t ht ((fun x : Fin 1 → ℝ≥0∞ => x 0) ⁻¹' s) (measurable_pi_apply 0 hs)
  have e1 : {ω | (fun i : ℕ => M.W (0 + 1 + i) ω) ∈ t} ∩
      {ω | (fun i : Fin (0 + 1) => M.T i ω) ∈ (fun x : Fin 1 → ℝ≥0∞ => x 0) ⁻¹' s} ∩
      {ω | M.T 0 ω ≤ M.Γ ω} = (fun ω => (M.T 0 ω, cyc M ω)) ⁻¹' (s ×ˢ t) ∩ S0 M := by
    ext ω
    simp only [zero_add, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, cyc,
      S0, Fin.val_zero]
    tauto
  have e2 : {ω | (fun i : Fin (0 + 1) => M.T i ω) ∈ (fun x : Fin 1 → ℝ≥0∞ => x 0) ⁻¹' s} ∩
      {ω | M.T 0 ω ≤ M.Γ ω} = M.T 0 ⁻¹' s ∩ S0 M := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, S0, Fin.val_zero]
  rw [e1, e2] at h
  exact h

include hP in
/-- the delay decomposition of the numerator -/
lemma numerator_identity (hreg : M.IsWideSenseTabooRegen) (k : ℕ)
    (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) (t : ℝ) (ht : 0 ≤ t) :
    M.P {ω | k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧ ENNReal.ofReal t < M.Γ ω} =
      ∫⁻ ω in S0 M, (if M.T 0 ω ≤ ENNReal.ofReal t then
        M.Q {ω'' | (t - (M.T 0 ω).toReal, cyc M ω'') ∈ Cset (A := A) k B} else 0) ∂M.P := by
  have := M.isProb
  have := Q_finite M
  have hg : Measurable fun ω => (M.T 0 ω, cyc M ω) := (M.measurable_T 0).prodMk (measurable_cyc M)
  set D : Set (ℝ≥0∞ × (ℕ → Path S)) :=
    {p | p.1 ≤ ENNReal.ofReal t ∧ (t - p.1.toReal, p.2) ∈ Cset (A := A) k B} with hDdef
  have hC := measurableSet_Cset M.exit_measurable k B hB
  have hD : MeasurableSet D := by
    refine (measurableSet_le measurable_fst measurable_const).inter ?_
    have hm : Measurable fun p : ℝ≥0∞ × (ℕ → Path S) => (t - p.1.toReal, p.2) :=
      (measurable_const.sub measurable_fst.ennreal_toReal).prodMk measurable_snd
    exact hm hC
  have hset : {ω | k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧ ENNReal.ofReal t < M.Γ ω} =
      (fun ω => (M.T 0 ω, cyc M ω)) ⁻¹' D ∩ S0 M := by
    ext ω
    rw [Set.mem_setOf_eq, delayed_event_iff M hP k B t ht ω]
    simp only [Set.mem_inter_iff, Set.mem_preimage, hDdef, Set.mem_setOf_eq]
    tauto
  rw [hset, ← Measure.restrict_apply (hg hD), ← Measure.map_apply hg hD, prod_law M hreg,
    Measure.prod_apply hD, lintegral_map (measurable_measure_prodMk_left hD) (M.measurable_T 0)]
  refine lintegral_congr fun ω => ?_
  rw [Measure.map_apply (measurable_cyc M) (measurable_prodMk_left hD)]
  split_ifs with h
  · congr 1
    ext x
    simp only [Set.mem_preimage, hDdef, Set.mem_setOf_eq, h, true_and]
  · have : cyc M ⁻¹' (Prod.mk (M.T 0 ω) ⁻¹' D) = ∅ := by
      ext x
      simp only [Set.mem_preimage, hDdef, Set.mem_setOf_eq, h, false_and, Set.mem_empty_iff_false]
    rw [this, measure_empty]

include hP in
lemma shifted_event_measure (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (u : ℝ) :
    M.Q {ω'' | (u, cyc M ω'') ∈ Cset (A := A) k B} =
      (shiftModel M hP).P {ω' | k < (shiftModel M hP).strad u ω' ∧
        ((shiftModel M hP).win k u ω', (shiftModel M hP).age u ω') ∈ B ∧
        ENNReal.ofReal u < (shiftModel M hP).Γ ω'} := by
  rw [← sh_Q M hP, ← sh_measure M hP]
  congr 1
  ext ω'
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [event_iff_Cset _ ω' (sh_T0 M hP ω'), sh_cyc]

end Identity

end TabooRegen.DelayShift

open TabooRegen TabooRegen.Model in
/-- **Delay reduction** (Glynn & Thorisson 2004, proof of Theorem 2 / Proposition 3: condition on
`T(0)`): a delayed taboo-regenerative model reduces to its non-delayed version on `{T(0) ⩽ Γ}`. -/
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (hP : M.P {ω | M.T 0 ω ≤ M.Γ ω} ≠ 0) :
    ∃ M' : Model S A {ω // M.T 0 ω ≤ M.Γ ω},
      M'.IsWideSenseTabooRegen ∧ (∀ ω, M'.T 0 ω = 0) ∧
      (∀ α, M'.A1 α ↔ M.A1 α) ∧ (M'.A2 ↔ M.A2) ∧ (∀ α, M'.A3 α ↔ M.A3 α) ∧
      (∀ α, M'.A4 α ↔ M.A4 α) ∧ (M'.A7 ↔ M.A7) ∧
      (∀ α, M'.rate α = M.rate α) ∧ (∀ α, M'.cycleWeight α = M.cycleWeight α) ∧
      (∀ α k (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)), M'.PstarNum α k B = M.PstarNum α k B) ∧
      ∀ (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)), MeasurableSet B → ∀ t : ℝ, 0 ≤ t →
        M.P {ω | k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧ ENNReal.ofReal t < M.Γ ω} =
          ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, (if M.T 0 ω ≤ ENNReal.ofReal t then
            M'.P {ω' | k < M'.strad (t - (M.T 0 ω).toReal) ω' ∧
              (M'.win k (t - (M.T 0 ω).toReal) ω', M'.age (t - (M.T 0 ω).toReal) ω') ∈ B ∧
              ENNReal.ofReal (t - (M.T 0 ω).toReal) < M'.Γ ω'} else 0) ∂M.P := by
  refine ⟨DelayShift.shiftModel M hP, DelayShift.sh_hreg M hP hreg, DelayShift.sh_T0 M hP,
    DelayShift.sh_A1 M hP, DelayShift.sh_A2 M hP, DelayShift.sh_A3 M hP, DelayShift.sh_A4 M hP,
    DelayShift.sh_A7 M hP, DelayShift.sh_rate M hP, DelayShift.sh_cycleWeight M hP,
    DelayShift.sh_PstarNum M hP, ?_⟩
  intro k B hB t ht
  rw [DelayShift.numerator_identity M hP hreg k B hB t ht]
  refine lintegral_congr fun ω => ?_
  split_ifs
  · exact DelayShift.shifted_event_measure M hP k B _
  · rfl
