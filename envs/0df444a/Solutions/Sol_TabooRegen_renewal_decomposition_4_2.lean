-- Prove2me | solution 1 for TabooRegen.renewal_decomposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T14:44:39.59442+00:00
-- url     : https://prove2.me/submissions/c5fa1d8e-7fdf-453a-b9f9-9d6f251bd2ea

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

namespace TabooRegen.Regen

open TabooRegen TabooRegen.Model TabooRegen.DelayShift

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- the future cycles after `T(j)`: `W_{j+1}, W_{j+2}, …` -/
def cycj (j : ℕ) (ω : Ω) : ℕ → Path S := fun i => M.W (j + 1 + i) ω

lemma measurable_cycj (j : ℕ) : Measurable (cycj M j) :=
  measurable_pi_lambda _ fun i => M.measurable_W (j + 1 + i)

lemma measurable_cyc' : Measurable (cyc M) :=
  measurable_pi_lambda _ fun i => M.measurable_W (1 + i)

lemma Q_finite' : IsFiniteMeasure M.Q := by
  have := M.isProb
  unfold Model.Q
  infer_instance

lemma measurableSet_le_Γ (j : ℕ) : MeasurableSet {ω | M.T j ω ≤ M.Γ ω} :=
  measurableSet_le (M.measurable_T j) (measurable_Γ M)

/-- Definition 2 at `n = j`: the joint law of `(T(j), W_{j+1}, W_{j+2}, …)` on `{T(j) ⩽ Γ}` is a product. -/
lemma prod_law_j (hreg : M.IsWideSenseTabooRegen) (j : ℕ) :
    (M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map (fun ω => (M.T j ω, cycj M j ω)) =
      ((M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map (M.T j)).prod (M.Q.map (cyc M)) := by
  have := M.isProb
  have := Q_finite' M
  have hg : Measurable fun ω => (M.T j ω, cycj M j ω) :=
    (M.measurable_T j).prodMk (measurable_cycj M j)
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hg (hs.prod ht), Measure.map_apply (M.measurable_T j) hs,
    Measure.map_apply (measurable_cyc' M) ht, Measure.restrict_apply (hg (hs.prod ht)),
    Measure.restrict_apply ((M.measurable_T j) hs)]
  have h := hreg j t ht ((fun x : Fin (j + 1) → ℝ≥0∞ => x (Fin.last j)) ⁻¹' s)
    (measurable_pi_apply _ hs)
  have e1 : {ω | (fun i : ℕ => M.W (j + 1 + i) ω) ∈ t} ∩
      {ω | (fun i : Fin (j + 1) => M.T i ω) ∈ (fun x : Fin (j + 1) → ℝ≥0∞ => x (Fin.last j)) ⁻¹' s} ∩
      {ω | M.T j ω ≤ M.Γ ω} =
        (fun ω => (M.T j ω, cycj M j ω)) ⁻¹' (s ×ˢ t) ∩ {ω | M.T j ω ≤ M.Γ ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, cycj,
      Fin.val_last]
    tauto
  have e2 : {ω | (fun i : Fin (j + 1) => M.T i ω) ∈
      (fun x : Fin (j + 1) → ℝ≥0∞ => x (Fin.last j)) ⁻¹' s} ∩ {ω | M.T j ω ≤ M.Γ ω} =
        M.T j ⁻¹' s ∩ {ω | M.T j ω ≤ M.Γ ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Fin.val_last]
  rw [e1, e2] at h
  exact h

lemma T_mono' {ω : Ω} {i n : ℕ} (h : i ≤ n) : M.T i ω ≤ M.T n ω :=
  (monotone_nat_of_le_succ fun m => M.T_mono m ω) h

/-- a visit of `X` to `Aᶜ` bounds `Γ` -/
lemma Γ_le_of_not_mem {ω : Ω} {r : ℝ≥0} (hr : M.X ω r ∉ A) : M.Γ ω ≤ (r : ℝ≥0∞) := by
  unfold Model.Γ exitTime
  exact iInf₂_le r ⟨M.X ω r, hr, rfl⟩

/-- before `Γ` no completed cycle exits `A` -/
lemma γ_top_of_le {ω : Ω} {n : ℕ} (h : M.T n ω ≤ M.Γ ω) {i : ℕ} (hi : i ≤ n) :
    M.γ i ω = ⊤ := by
  unfold Model.γ exitTime
  refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun ht => ?_
  exfalso
  obtain ⟨a, ha, hxa⟩ := ht
  rw [M.W_eq] at hxa
  unfold cycleOf at hxa
  split_ifs at hxa with hlt
  · have hfin : prevTime M.T i ω + (t : ℝ≥0∞) ≠ ⊤ := ne_top_of_lt hlt
    have hX : M.X ω (prevTime M.T i ω + (t : ℝ≥0∞)).toNNReal ∉ A := by
      rw [Sum.inl.injEq] at hxa; rw [hxa]; exact ha
    have h1 := Γ_le_of_not_mem M hX
    rw [ENNReal.coe_toNNReal hfin] at h1
    have h2 : M.T i ω ≤ M.Γ ω := (T_mono' M hi).trans h
    exact absurd (h1.trans_lt (hlt.trans_le h2)) (lt_irrefl _)

/-- a cycle without exit after `T(n) ⩽ Γ` keeps `T(n+1) ⩽ Γ` -/
lemma le_Γ_succ {ω : Ω} {n : ℕ} (h : M.T n ω ≤ M.Γ ω) (hγ : M.γ (n + 1) ω = ⊤) :
    M.T (n + 1) ω ≤ M.Γ ω := by
  by_contra hcon
  rw [not_le] at hcon
  have hTtop : M.T (n + 1) ω = ⊤ := M.taboo (n + 1) ω hcon
  have hΓtop : M.Γ ω < ⊤ := M.T_top (n + 1) ω hTtop
  -- a visit to `Aᶜ`
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, M.X ω r ∉ A := by
    by_contra hno
    push_neg at hno
    have : M.Γ ω = ⊤ := by
      unfold Model.Γ exitTime
      refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun ht => ?_
      obtain ⟨a, ha, hxa⟩ := ht
      rw [Sum.inl.injEq] at hxa
      exact absurd (hxa ▸ hno t) ha
    exact absurd this hΓtop.ne
  have hTn : M.T n ω ≠ ⊤ := ne_top_of_le_ne_top hΓtop.ne h
  have hrT : M.T n ω ≤ (r : ℝ≥0∞) := h.trans (Γ_le_of_not_mem M hr)
  set c := (M.T n ω).toNNReal with hc
  have hcT : (c : ℝ≥0∞) = M.T n ω := ENNReal.coe_toNNReal hTn
  have hcr : c ≤ r := by rw [← ENNReal.coe_le_coe, hcT]; exact hrT
  have hW : (M.W (n + 1) ω).1 (r - c) = Sum.inl (M.X ω r) := by
    rw [M.W_eq]
    unfold cycleOf
    have hp : prevTime M.T (n + 1) ω = (c : ℝ≥0∞) := by simp [prevTime, hcT]
    rw [hp, ← ENNReal.coe_add, add_tsub_cancel_of_le hcr, if_pos (by rw [hTtop]; exact ENNReal.coe_lt_top)]
    simp
  have : M.γ (n + 1) ω ≤ ((r - c : ℝ≥0) : ℝ≥0∞) := by
    unfold Model.γ exitTime
    exact iInf₂_le (r - c) ⟨M.X ω r, hr, hW⟩
  rw [hγ] at this
  exact absurd this (by simp)

/-- on `{T(n) ⩽ Γ}`: `T(n+1) ⩽ Γ ↔ γ_{n+1} = ∞` -/
lemma le_Γ_succ_iff {ω : Ω} {n : ℕ} (h : M.T n ω ≤ M.Γ ω) :
    M.T (n + 1) ω ≤ M.Γ ω ↔ M.γ (n + 1) ω = ⊤ :=
  ⟨fun h' => γ_top_of_le M h' le_rfl, le_Γ_succ M h⟩

end TabooRegen.Regen

namespace TabooRegen.Twist

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- the exponential density -/
noncomputable def ed (α : ℝ) (u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (α * u))

lemma measurable_ed (α : ℝ) : Measurable (ed α) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal

lemma ed_add (α u v : ℝ) : ed α (u + v) = ed α u * ed α v := by
  unfold ed; rw [mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

lemma measurable_τ' (n : ℕ) : Measurable (M.τ n) := by
  have hTm : Measurable (M.Tm n) := by
    by_cases hn : n = 0
    · have : M.Tm n = fun _ => 0 := by funext ω; simp [Model.Tm, prevTime, hn]
      rw [this]; exact measurable_const
    · have : M.Tm n = M.T (n - 1) := by funext ω; simp [Model.Tm, prevTime, hn]
      rw [this]; exact M.measurable_T _
  unfold Model.τ
  exact (M.measurable_T n).sub hTm

lemma measurableSet_NoExit (n : ℕ) : MeasurableSet (M.NoExit n) :=
  (M.exit_measurable.comp (M.measurable_W n)) (measurableSet_singleton ⊤)

/-- the twisted functional `E[e^{α T(j)} f(T(j)); T(j) ⩽ Γ]` -/
noncomputable def K (α : ℝ) (j : ℕ) (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | M.T j ω ≤ M.Γ ω}, ed α (M.T j ω).toReal * f (M.T j ω).toReal ∂M.P

lemma lintegral_L (α : ℝ) (j : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u, f u ∂(((M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map fun ω => (M.T j ω).toReal).withDensity
        (fun u => ENNReal.ofReal (Real.exp (α * u)))) = K M α j f := by
  rw [show (fun u : ℝ => ENNReal.ofReal (Real.exp (α * u))) = ed α from rfl,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_ed α) hf,
    lintegral_map ((measurable_ed α).mul hf) (M.measurable_T j).ennreal_toReal]
  rfl

lemma lintegral_Gtilde (α : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(M.Gtilde α) =
      ∫⁻ ω in M.NoExit 1, ed α (M.τ 1 ω).toReal * f (M.τ 1 ω).toReal ∂M.Q := by
  unfold Model.Gtilde Model.G
  rw [show (fun x : ℝ => ENNReal.ofReal (Real.exp (α * x))) = ed α from rfl,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_ed α) hf,
    lintegral_map ((measurable_ed α).mul hf) (measurable_τ' M 1).ennreal_toReal]
  rfl

lemma inner_eq (α : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) (v : ℝ) :
    ∫⁻ ω in M.NoExit 1, ed α (v + (M.τ 1 ω).toReal) * f (v + (M.τ 1 ω).toReal) ∂M.Q =
      ed α v * ∫⁻ y, f (v + y) ∂(M.Gtilde α) := by
  have hfv : Measurable fun y => f (v + y) := hf.comp (measurable_const_add v)
  rw [lintegral_Gtilde M α hfv, ← lintegral_const_mul' (ed α v) _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  rw [ed_add, mul_assoc]

lemma sfinite_Gtilde (α : ℝ) : SFinite (M.Gtilde α) := by
  have := Q_finite' M
  unfold Model.Gtilde Model.G
  infer_instance

lemma measurable_conv_fun (α : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun u => ∫⁻ y, f (u + y) ∂(M.Gtilde α) := by
  have := sfinite_Gtilde M α
  exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => f (p.1 + p.2))
    (hf.comp measurable_add)

lemma K_succ (hreg : M.IsWideSenseTabooRegen) (α : ℝ) (j : ℕ) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    K M α (j + 1) f = K M α j (fun u => ∫⁻ y, f (u + y) ∂(M.Gtilde α)) := by
  have := M.isProb
  have := Q_finite' M
  set F : ℝ → ℝ≥0∞ := fun u => ed α u * f u with hF
  have hFm : Measurable F := (measurable_ed α).mul hf
  set Z : Set (ℝ≥0∞ × (ℕ → Path S)) := {p | exitTime A (p.2 0).1 = ⊤} with hZ
  have hZm : MeasurableSet Z :=
    (M.exit_measurable.comp ((measurable_pi_apply 0).comp measurable_snd)) (measurableSet_singleton ⊤)
  set g : ℝ≥0∞ × (ℕ → Path S) → ℝ≥0∞ :=
    Z.indicator (fun p => F (p.1.toReal + (len (p.2 0)).toReal)) with hg
  have hgm : Measurable g :=
    (hFm.comp (measurable_fst.ennreal_toReal.add
      ((measurable_len.comp ((measurable_pi_apply 0).comp measurable_snd)).ennreal_toReal))).indicator hZm
  have hE : {ω | M.T (j + 1) ω ≤ M.Γ ω} = {ω | M.γ (j + 1) ω = ⊤} ∩ {ω | M.T j ω ≤ M.Γ ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      have h' : M.T j ω ≤ M.Γ ω := (M.T_mono j ω).trans h
      exact ⟨(le_Γ_succ_iff M h').1 h, h'⟩
    · rintro ⟨h1, h2⟩
      exact (le_Γ_succ_iff M h2).2 h1
  have hγm : MeasurableSet {ω | M.γ (j + 1) ω = ⊤} := measurableSet_NoExit M (j + 1)
  have step1 : K M α (j + 1) f =
      ∫⁻ ω in {ω | M.T j ω ≤ M.Γ ω}, g (M.T j ω, cycj M j ω) ∂M.P := by
    unfold K
    rw [hE, ← Measure.restrict_restrict hγm, ← lintegral_indicator hγm]
    refine lintegral_congr_ae ((ae_restrict_mem (measurableSet_le_Γ M j)).mono fun ω hω => ?_)
    have hω' : M.T j ω ≤ M.Γ ω := hω
    have hc0 : cycj M j ω 0 = M.W (j + 1) ω := by simp [cycj]
    by_cases hγ : M.γ (j + 1) ω = ⊤
    · have hle : M.T (j + 1) ω ≤ M.Γ ω := (le_Γ_succ_iff M hω').2 hγ
      have hfin : M.T (j + 1) ω ≠ ⊤ := by
        intro h
        have h2 := M.T_top (j + 1) ω h
        rw [h, top_le_iff] at hle
        exact (ne_of_lt h2) hle
      have hlen : len (M.W (j + 1) ω) = M.T (j + 1) ω - M.T j ω := by
        rw [len_W]; simp [Model.τ, Model.Tm, prevTime]
      have hsum : (M.T (j + 1) ω).toReal = (M.T j ω).toReal + (len (M.W (j + 1) ω)).toReal := by
        rw [hlen, ENNReal.toReal_sub_of_le (M.T_mono j ω) hfin]; ring
      have hmemZ : (M.T j ω, cycj M j ω) ∈ Z := by
        simp only [hZ, Set.mem_setOf_eq, hc0]; exact hγ
      rw [Set.indicator_of_mem (show ω ∈ {ω | M.γ (j + 1) ω = ⊤} from hγ)]
      show _ = g (M.T j ω, cycj M j ω)
      rw [hg, Set.indicator_of_mem hmemZ]
      simp only [hF, hc0, hsum]
    · have hmemZ : (M.T j ω, cycj M j ω) ∉ Z := by
        simp only [hZ, Set.mem_setOf_eq, hc0]; exact hγ
      rw [Set.indicator_of_notMem (show ω ∉ {ω | M.γ (j + 1) ω = ⊤} from hγ)]
      show _ = g (M.T j ω, cycj M j ω)
      rw [hg, Set.indicator_of_notMem hmemZ]
  have step2 : ∫⁻ ω in {ω | M.T j ω ≤ M.Γ ω}, g (M.T j ω, cycj M j ω) ∂M.P =
      ∫⁻ v, ∫⁻ x, g (v, x) ∂(M.Q.map (cyc M))
        ∂((M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map (M.T j)) := by
    have h := lintegral_map hgm ((M.measurable_T j).prodMk (measurable_cycj M j))
      (μ := M.P.restrict {ω | M.T j ω ≤ M.Γ ω})
    rw [prod_law_j M hreg j, lintegral_prod _ hgm.aemeasurable] at h
    exact h.symm
  have step3 : ∀ v : ℝ≥0∞, ∫⁻ x, g (v, x) ∂(M.Q.map (cyc M)) =
      ed α v.toReal * ∫⁻ y, f (v.toReal + y) ∂(M.Gtilde α) := by
    intro v
    have hgv : Measurable fun x => g (v, x) := hgm.comp measurable_prodMk_left
    rw [lintegral_map hgv (measurable_cyc' M), ← inner_eq M α hf v.toReal,
      ← lintegral_indicator (measurableSet_NoExit M 1)]
    refine lintegral_congr fun ω => ?_
    have hc : cyc M ω 0 = M.W 1 ω := by simp [cyc]
    by_cases hγ : M.γ 1 ω = ⊤
    · have hmemZ : (v, cyc M ω) ∈ Z := by
        simp only [hZ, Set.mem_setOf_eq, hc]; exact hγ
      rw [hg, Set.indicator_of_mem hmemZ, Set.indicator_of_mem (show ω ∈ M.NoExit 1 from hγ)]
      simp only [hF, hc, len_W]
    · have hmemZ : (v, cyc M ω) ∉ Z := by
        simp only [hZ, Set.mem_setOf_eq, hc]; exact hγ
      rw [hg, Set.indicator_of_notMem hmemZ, Set.indicator_of_notMem (show ω ∉ M.NoExit 1 from hγ)]
  rw [step1, step2]
  simp_rw [step3]
  unfold K
  have hmeas : Measurable fun v : ℝ≥0∞ => ed α v.toReal * ∫⁻ y, f (v.toReal + y) ∂(M.Gtilde α) :=
    ((measurable_ed α).comp ENNReal.measurable_toReal).mul
      ((measurable_conv_fun M α hf).comp ENNReal.measurable_toReal)
  rw [lintegral_map hmeas (M.measurable_T j)]

lemma K_zero (h0 : ∀ ω, M.T 0 ω = 0) (α : ℝ) (f : ℝ → ℝ≥0∞) : K M α 0 f = f 0 := by
  have := M.isProb
  have hE : {ω | M.T 0 ω ≤ M.Γ ω} = Set.univ := by ext ω; simp [h0]
  unfold K
  rw [hE, Measure.restrict_univ]
  simp [h0, ed]

theorem K_eq_conv (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) (α : ℝ) (j : ℕ) :
    ∀ f : ℝ → ℝ≥0∞, Measurable f →
      K M α j f = ∫⁻ u, f u ∂(QueueingFundamentals.MG1.convPow (M.Gtilde α) j) := by
  have := sfinite_Gtilde M α
  induction j with
  | zero =>
    intro f hf
    rw [K_zero M h0]
    simp [QueueingFundamentals.MG1.convPow]
  | succ j ih =>
    intro f hf
    rw [K_succ M hreg α j hf, ih _ (measurable_conv_fun M α hf), QueueingFundamentals.MG1.convPow,
      Measure.lintegral_conv hf]

theorem twisted_law (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) (α : ℝ) (j : ℕ) :
    ((M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map fun ω => (M.T j ω).toReal).withDensity
        (fun u => ENNReal.ofReal (Real.exp (α * u))) =
      QueueingFundamentals.MG1.convPow (M.Gtilde α) j := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_L M α j hf, K_eq_conv M hreg h0 α j f hf]

end TabooRegen.Twist

namespace TabooRegen.Decomp

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen TabooRegen.Twist

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

lemma measurable_btilde' (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) : Measurable (M.btilde α ℓ B) := by
  have h1 : Measurable fun p : ℝ × Ω =>
      ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) p.2), p.1 - (M.T ℓ p.2).toReal) :=
    (measurable_pi_lambda _ fun i => (M.measurable_W _).comp measurable_snd).prodMk
      (measurable_fst.sub ((M.measurable_T ℓ).ennreal_toReal.comp measurable_snd))
  have hE : MeasurableSet {p : ℝ × Ω |
      ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) p.2), p.1 - (M.T ℓ p.2).toReal) ∈ B ∧
      M.T ℓ p.2 ≤ ENNReal.ofReal p.1 ∧ ENNReal.ofReal p.1 < M.T (ℓ + 1) p.2 ∧
      ENNReal.ofReal p.1 < M.Γ p.2} :=
    (hB.preimage h1).inter ((measurableSet_le ((M.measurable_T ℓ).comp measurable_snd)
      (ENNReal.measurable_ofReal.comp measurable_fst)).inter
      ((measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((M.measurable_T (ℓ + 1)).comp measurable_snd)).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((measurable_Γ M).comp measurable_snd))))
  haveI : IsProbabilityMeasure M.P := M.isProb
  have h2 := (measurable_measure_prodMk_left (ν := M.P) hE).ennreal_toReal
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul h2

/-- the non-delayed `b̃` event at time `s`, read off cycles -/
def Dp (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (s : ℝ) (x : ℕ → Path S) : Prop :=
  ((fun i : Fin (2 * k + 1) => x i), s - (Tx x k).toReal) ∈ B ∧ Tx x k ≤ ENNReal.ofReal s ∧
    ENNReal.ofReal s < Tx x (k + 1) ∧ ENNReal.ofReal s < Ψx (A := A) x

/-- the event after `T(j) = w`, as a set of `(w, W_{j+1}, …)` -/
def Dset (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (t : ℝ) :
    Set (ℝ≥0∞ × (ℕ → Path S)) :=
  {p | p.1 ≤ ENNReal.ofReal t ∧ Dp (A := A) k B (t - p.1.toReal) p.2}

lemma measurableSet_Dp (hγ : Measurable fun x : Path S => exitTime A x.1) (k : ℕ)
    (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) (s : ℝ) :
    MeasurableSet {x : ℕ → Path S | Dp (A := A) k B s x} := by
  have hg : Measurable fun x : ℕ → Path S =>
      ((fun i : Fin (2 * k + 1) => x i), s - (Tx x k).toReal) :=
    (measurable_pi_lambda _ fun i => measurable_pi_apply _).prodMk
      (measurable_const.sub (measurable_Tx k).ennreal_toReal)
  exact (hB.preimage hg).inter ((measurableSet_le (measurable_Tx k) measurable_const).inter
    ((measurableSet_lt measurable_const (measurable_Tx (k + 1))).inter
      (measurableSet_lt measurable_const (measurable_Ψx hγ))))

lemma measurableSet_Dset (hγ : Measurable fun x : Path S => exitTime A x.1) (k : ℕ)
    (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) (t : ℝ) :
    MeasurableSet (Dset (A := A) k B t) := by
  have hs : Measurable fun p : ℝ≥0∞ × (ℕ → Path S) => t - p.1.toReal :=
    measurable_const.sub measurable_fst.ennreal_toReal
  have hg : Measurable fun p : ℝ≥0∞ × (ℕ → Path S) =>
      ((fun i : Fin (2 * k + 1) => p.2 i), (t - p.1.toReal) - (Tx p.2 k).toReal) :=
    (measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_snd).prodMk
      (hs.sub ((measurable_Tx k).comp measurable_snd).ennreal_toReal)
  exact (measurableSet_le measurable_fst measurable_const).inter ((hB.preimage hg).inter
    ((measurableSet_le ((measurable_Tx k).comp measurable_snd) hs.ennreal_ofReal).inter
      ((measurableSet_lt hs.ennreal_ofReal ((measurable_Tx (k + 1)).comp measurable_snd)).inter
        (measurableSet_lt hs.ennreal_ofReal ((measurable_Ψx hγ).comp measurable_snd)))))

lemma T_add_eq (j : ℕ) (ω : Ω) (hj : M.T j ω ≠ ⊤) (n : ℕ) :
    M.T (j + n) ω = M.T j ω + Tx (cycj M j ω) n := by
  induction n with
  | zero => simp [Tx]
  | succ n ih =>
    rw [Tx, Finset.sum_range_succ, ← Tx,
      show M.T j ω + (Tx (cycj M j ω) n + len (cycj M j ω n)) =
        (M.T j ω + Tx (cycj M j ω) n) + len (cycj M j ω n) from (add_assoc _ _ _).symm, ← ih]
    have hc : cycj M j ω n = M.W (j + n + 1) ω := by
      simp only [cycj]; congr 1; omega
    rw [hc, len_W]
    have hτ : M.τ (j + n + 1) ω = M.T (j + n + 1) ω - M.T (j + n) ω := by
      simp [Model.τ, Model.Tm, prevTime]
    rw [hτ]
    show M.T (j + n + 1) ω = _
    by_cases hT : M.T (j + n) ω = ⊤
    · have h1 : M.T (j + n + 1) ω = ⊤ := top_le_iff.1 (hT ▸ M.T_mono (j + n) ω)
      rw [hT, h1]; simp
    · exact (add_tsub_cancel_of_le (M.T_mono (j + n) ω)).symm

lemma Ψ_shift (j : ℕ) (ω : Ω) (hj : M.T j ω ≤ M.Γ ω) (hjt : M.T j ω ≠ ⊤) :
    Ψ M ω = M.T j ω + Ψx (A := A) (cycj M j ω) := by
  have key : ∀ m : ℕ, M.Tm (j + 1 + m) ω + M.γ (j + 1 + m) ω =
      M.T j ω + (Tx (cycj M j ω) m + exitTime A (cycj M j ω m).1) := by
    intro m
    have h1 : M.Tm (j + 1 + m) ω = M.T (j + m) ω := by
      rw [show j + 1 + m = (j + m) + 1 by omega]; simp [Model.Tm, prevTime]
    have h2 : M.γ (j + 1 + m) ω = exitTime A (cycj M j ω m).1 := rfl
    rw [h1, h2, T_add_eq M j ω hjt m, add_assoc]
  unfold Ψ Ψx
  rw [ENNReal.add_iInf]
  apply le_antisymm
  · exact le_iInf fun m => (iInf_le _ (j + 1 + m)).trans (le_of_eq (key m))
  · refine le_iInf fun i => ?_
    by_cases hi : i ≤ j
    · rw [γ_top_of_le M hj hi, add_top]; exact le_top
    · obtain ⟨m, rfl⟩ : ∃ m, i = j + 1 + m := ⟨i - (j + 1), by omega⟩
      exact (iInf_le _ m).trans (le_of_eq (key m).symm)

lemma strad_eq_succ_iff (u : ℝ) (ω : Ω) (n : ℕ) :
    M.strad u ω = n + 1 ↔ ENNReal.ofReal u < M.T (n + 1) ω ∧ M.T n ω ≤ ENNReal.ofReal u := by
  unfold Model.strad
  constructor
  · intro h
    have hne : {m : ℕ | ENNReal.ofReal u < M.T m ω}.Nonempty := by
      by_contra he
      rw [Set.not_nonempty_iff_eq_empty] at he
      rw [he, Nat.sInf_empty] at h
      omega
    have h1 := Nat.sInf_mem hne
    rw [h] at h1
    refine ⟨h1, ?_⟩
    have h2 := Nat.notMem_of_lt_sInf (show n < sInf {m : ℕ | ENNReal.ofReal u < M.T m ω} by omega)
    exact not_lt.1 h2
  · rintro ⟨h1, h2⟩
    apply le_antisymm (Nat.sInf_le h1)
    refine le_csInf ⟨_, h1⟩ fun m hm => ?_
    by_contra hmn
    have : M.T m ω ≤ M.T n ω := T_mono' M (by omega)
    exact absurd hm (not_lt.2 (this.trans h2))

lemma win_age_eq (k : ℕ) (t : ℝ) (j : ℕ) (ω : Ω) (hs : M.strad t ω = j + k + 1)
    (hjt : M.T j ω ≠ ⊤) (hk : Tx (cycj M j ω) k ≠ ⊤) :
    (M.win k t ω, M.age t ω) = ((fun i : Fin (2 * k + 1) => cycj M j ω i),
      (t - (M.T j ω).toReal) - (Tx (cycj M j ω) k).toReal) := by
  have hTm : M.Tm (M.strad t ω) ω = M.T (j + k) ω := by
    rw [hs]; simp [Model.Tm, prevTime]
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext i
    show M.W (M.strad t ω - k + i) ω = M.W (j + 1 + i) ω
    rw [hs]
    congr 1
    omega
  · show t - (M.Tm (M.strad t ω) ω).toReal = _
    rw [hTm, T_add_eq M j ω hjt k, ENNReal.toReal_add hjt hk]
    ring

lemma event_j (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (t : ℝ) (ht : 0 ≤ t) (j : ℕ)
    (ω : Ω) :
    ((k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧ ENNReal.ofReal t < M.Γ ω) ∧
        M.strad t ω = j + k + 1) ↔
      ω ∈ {ω | M.T j ω ≤ M.Γ ω} ∩ (fun ω => (M.T j ω, cycj M j ω)) ⁻¹' Dset (A := A) k B t := by
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Dset, Dp]
  have hk0 : M.T j ω ≠ ⊤ → M.T (j + k) ω = M.T j ω + Tx (cycj M j ω) k :=
    fun h => T_add_eq M j ω h k
  have hk1 : M.T j ω ≠ ⊤ → M.T (j + k + 1) ω = M.T j ω + Tx (cycj M j ω) (k + 1) :=
    fun h => T_add_eq M j ω h (k + 1)
  constructor
  · rintro ⟨⟨hk, hB, hΓ⟩, hs⟩
    obtain ⟨hs1, hs2⟩ := (strad_eq_succ_iff M t ω (j + k)).1 hs
    have hTj : M.T j ω ≤ ENNReal.ofReal t := (T_mono' M (by omega : j ≤ j + k)).trans hs2
    have hjt : M.T j ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTj
    have hjΓ : M.T j ω ≤ M.Γ ω := hTj.trans hΓ.le
    have hΨ := (lt_Γ_iff_lt_Ψ M ω (j + k + 1) _ hs1).1 hΓ
    rw [Ψ_shift M j ω hjΓ hjt] at hΨ
    have hvt : (M.T j ω).toReal ≤ t := ENNReal.toReal_le_of_le_ofReal ht hTj
    set v := (M.T j ω).toReal with hvdef
    have hv : M.T j ω = ENNReal.ofReal v := (ENNReal.ofReal_toReal hjt).symm
    have hsplit : ENNReal.ofReal t = ENNReal.ofReal v + ENNReal.ofReal (t - v) := by
      rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg (by linarith)]; congr 1; ring
    rw [hk0 hjt, hsplit, hv] at hs2
    rw [hk1 hjt, hsplit, hv] at hs1
    rw [hsplit, hv] at hΨ
    have hA := (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 hs2
    rw [win_age_eq M k t j ω hs hjt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA)] at hB
    exact ⟨hjΓ, hTj, hB, hA, (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).1 hs1,
      (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).1 hΨ⟩
  · rintro ⟨hjΓ, hTj, hB, hA, hA1, hΨ⟩
    have hjt : M.T j ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTj
    have hvt : (M.T j ω).toReal ≤ t := ENNReal.toReal_le_of_le_ofReal ht hTj
    have hk0' := hk0 hjt
    have hk1' := hk1 hjt
    set v := (M.T j ω).toReal with hvdef
    have hv : M.T j ω = ENNReal.ofReal v := (ENNReal.ofReal_toReal hjt).symm
    have hsplit : ENNReal.ofReal t = ENNReal.ofReal v + ENNReal.ofReal (t - v) := by
      rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg (by linarith)]; congr 1; ring
    have hs2 : M.T (j + k) ω ≤ ENNReal.ofReal t := by
      rw [hk0', hsplit, hv]; exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).2 hA
    have hs1 : ENNReal.ofReal t < M.T (j + k + 1) ω := by
      rw [hk1', hsplit, hv]; exact (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).2 hA1
    have hs : M.strad t ω = j + k + 1 := (strad_eq_succ_iff M t ω (j + k)).2 ⟨hs1, hs2⟩
    refine ⟨⟨by omega, ?_, ?_⟩, hs⟩
    · rw [win_age_eq M k t j ω hs hjt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA)]; exact hB
    · rw [lt_Γ_iff_lt_Ψ M ω (j + k + 1) _ hs1, Ψ_shift M j ω hjΓ hjt, hsplit, hv]
      exact (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).2 hΨ

end TabooRegen.Decomp

namespace TabooRegen.Decomp

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen TabooRegen.Twist

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

lemma Q_eq_P (h0 : ∀ ω, M.T 0 ω = 0) : M.Q = M.P := by
  have := M.isProb
  have hE : {ω | M.T 0 ω ≤ M.Γ ω} = Set.univ := by ext ω; simp [h0]
  unfold Model.Q
  rw [hE, ProbabilityTheory.cond_univ]

lemma btilde_eq (h0 : ∀ ω, M.T 0 ω = 0) (α : ℝ) (k : ℕ)
    (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (s : ℝ) :
    M.btilde α k B s = Real.exp (α * s) * (M.P {ω | Dp (A := A) k B s (cyc M ω)}).toReal := by
  unfold Model.btilde
  congr 3
  ext ω
  have hT := T_eq_Tx M ω (h0 ω)
  simp only [Set.mem_setOf_eq, Dp]
  rw [hT k, hT (k + 1), ← Ψ_eq_Ψx M ω (h0 ω)]
  constructor
  · rintro ⟨hB, h1, h2, h3⟩
    have h2' : ENNReal.ofReal s < M.T (k + 1) ω := by rw [hT (k + 1)]; exact h2
    exact ⟨hB, h1, h2, (lt_Γ_iff_lt_Ψ M ω (k + 1) _ h2').1 h3⟩
  · rintro ⟨hB, h1, h2, h3⟩
    have h2' : ENNReal.ofReal s < M.T (k + 1) ω := by rw [hT (k + 1)]; exact h2
    exact ⟨hB, h1, h2, (lt_Γ_iff_lt_Ψ M ω (k + 1) _ h2').2 h3⟩

lemma per_j (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) (α : ℝ) (k : ℕ)
    (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) (t : ℝ) (ht : 0 ≤ t)
    (j : ℕ) :
    ENNReal.ofReal (Real.exp (α * t)) *
        M.P ({ω | M.T j ω ≤ M.Γ ω} ∩ (fun ω => (M.T j ω, cycj M j ω)) ⁻¹' Dset (A := A) k B t) =
      K M α j ((Set.Icc 0 t).indicator fun u => ENNReal.ofReal (M.btilde α k B (t - u))) := by
  have := M.isProb
  have := Q_finite' M
  have hD := measurableSet_Dset M.exit_measurable k B hB t
  have hg : Measurable fun ω => (M.T j ω, cycj M j ω) :=
    (M.measurable_T j).prodMk (measurable_cycj M j)
  have hf : Measurable ((Set.Icc 0 t).indicator fun u => ENNReal.ofReal (M.btilde α k B (t - u))) :=
    (((measurable_btilde' M α k B hB).comp (measurable_const.sub measurable_id)).ennreal_ofReal).indicator
      measurableSet_Icc
  have hmeas : Measurable fun w : ℝ≥0∞ => ed α w.toReal *
      (Set.Icc 0 t).indicator (fun u => ENNReal.ofReal (M.btilde α k B (t - u))) w.toReal :=
    ((measurable_ed α).comp ENNReal.measurable_toReal).mul (hf.comp ENNReal.measurable_toReal)
  have hK : K M α j ((Set.Icc 0 t).indicator fun u => ENNReal.ofReal (M.btilde α k B (t - u))) =
      ∫⁻ w, ed α w.toReal *
          (Set.Icc 0 t).indicator (fun u => ENNReal.ofReal (M.btilde α k B (t - u))) w.toReal
        ∂((M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map (M.T j)) := by
    unfold K; rw [lintegral_map hmeas (M.measurable_T j)]
  rw [hK, Set.inter_comm, ← Measure.restrict_apply (hg hD), ← Measure.map_apply hg hD,
    prod_law_j M hreg j, Measure.prod_apply hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : ∀ᵐ w ∂((M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map (M.T j)), w ≠ ⊤ := by
    rw [ae_map_iff (p := fun w : ℝ≥0∞ => w ≠ ⊤) (M.measurable_T j).aemeasurable
      (measurableSet_singleton ⊤).compl]
    filter_upwards [ae_restrict_mem (measurableSet_le_Γ M j)] with ω hω
    intro h
    have h2 := M.T_top j ω h
    have hle : M.T j ω ≤ M.Γ ω := hω
    rw [h, top_le_iff] at hle
    exact (ne_of_lt h2) hle
  refine lintegral_congr_ae (hfin.mono fun w hw => ?_)
  by_cases hwt : w ≤ ENNReal.ofReal t
  · have hsl : Prod.mk w ⁻¹' Dset (A := A) k B t = {x | Dp (A := A) k B (t - w.toReal) x} := by
      ext x; simp [Dset, hwt]
    have hvt : w.toReal ≤ t := ENNReal.toReal_le_of_le_ofReal ht hwt
    beta_reduce
    rw [hsl, Measure.map_apply (measurable_cyc' M) (measurableSet_Dp M.exit_measurable k B hB _),
      Q_eq_P M h0, Set.indicator_of_mem (show w.toReal ∈ Set.Icc 0 t from ⟨ENNReal.toReal_nonneg, hvt⟩)]
    beta_reduce
    rw [btilde_eq M h0, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have he : Real.exp (α * t) = Real.exp (α * w.toReal) * Real.exp (α * (t - w.toReal)) := by
      rw [← Real.exp_add]; ring_nf
    rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    all_goals rfl
  · have hsl : Prod.mk w ⁻¹' Dset (A := A) k B t = ∅ := by
      ext x; simp [Dset, hwt]
    have hvt : w.toReal ∉ Set.Icc 0 t := by
      rintro ⟨-, h⟩
      apply hwt
      rw [← ENNReal.ofReal_toReal hw]
      exact ENNReal.ofReal_le_ofReal h
    beta_reduce
    rw [hsl, measure_empty, mul_zero, Set.indicator_of_notMem hvt, mul_zero]

lemma sfinite_convPow (α : ℝ) (j : ℕ) :
    SFinite (QueueingFundamentals.MG1.convPow (M.Gtilde α) j) := by
  have := sfinite_Gtilde M α
  induction j with
  | zero => simp only [QueueingFundamentals.MG1.convPow]; infer_instance
  | succ j ih =>
    simp only [QueueingFundamentals.MG1.convPow]
    unfold Measure.conv
    infer_instance

theorem decomp_lintegral (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) (α : ℝ)
    (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) (t : ℝ)
    (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (α * t)) *
        M.P {ω | k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧ ENNReal.ofReal t < M.Γ ω} =
      ∫⁻ u in Set.Icc 0 t, ENNReal.ofReal (M.btilde α k B (t - u))
        ∂(SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) (M.Gtilde α)) := by
  have hU : {ω | k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧ ENNReal.ofReal t < M.Γ ω} =
      ⋃ j, ({ω | M.T j ω ≤ M.Γ ω} ∩
        (fun ω => (M.T j ω, cycj M j ω)) ⁻¹' Dset (A := A) k B t) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      have hk := h.1
      exact ⟨M.strad t ω - k - 1, (event_j M k B t ht _ ω).1 ⟨h, by omega⟩⟩
    · rintro ⟨j, hj⟩
      exact ((event_j M k B t ht j ω).2 hj).1
  have hm : ∀ j, MeasurableSet ({ω | M.T j ω ≤ M.Γ ω} ∩
      (fun ω => (M.T j ω, cycj M j ω)) ⁻¹' Dset (A := A) k B t) := fun j =>
    (measurableSet_le_Γ M j).inter (((M.measurable_T j).prodMk (measurable_cycj M j))
      (measurableSet_Dset M.exit_measurable k B hB t))
  have hd : Pairwise (Function.onFun Disjoint fun j => ({ω | M.T j ω ≤ M.Γ ω} ∩
      (fun ω => (M.T j ω, cycj M j ω)) ⁻¹' Dset (A := A) k B t)) := by
    intro i j hij
    refine Set.disjoint_left.2 fun ω hi hj => hij ?_
    have h1 := ((event_j M k B t ht i ω).2 hi).2
    have h2 := ((event_j M k B t ht j ω).2 hj).2
    omega
  have hf : Measurable ((Set.Icc 0 t).indicator fun u => ENNReal.ofReal (M.btilde α k B (t - u))) :=
    (((measurable_btilde' M α k B hB).comp (measurable_const.sub measurable_id)).ennreal_ofReal).indicator
      measurableSet_Icc
  rw [hU, measure_iUnion hd hm, ← ENNReal.tsum_mul_left, ← lintegral_indicator measurableSet_Icc]
  unfold SmithRegenerative.Equilibrium.renewalMeasure
  rw [lintegral_sum_measure]
  refine tsum_congr fun j => ?_
  have := sfinite_convPow M α j
  rw [per_j M hreg h0 α k B hB t ht j, K_eq_conv M hreg h0 α j _ hf, Measure.lintegral_conv hf,
    lintegral_dirac]
  simp only [zero_add]

theorem decomp_real (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) (α : ℝ)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) :
    Real.exp (α * t) *
        (M.P {ω | k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧
          ENNReal.ofReal t < M.Γ ω}).toReal =
      ∫ u in Set.Icc 0 t, M.btilde α k B (t - u)
        ∂(SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) (M.Gtilde α)) := by
  have hm : Measurable fun u => M.btilde α k B (t - u) :=
    (measurable_btilde' M α k B hB).comp (measurable_const.sub measurable_id)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => ?_)
      hm.aestronglyMeasurable, ← decomp_lintegral M hreg h0 α k B hB t ht, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  show 0 ≤ M.btilde α k B (t - u)
  unfold Model.btilde
  exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg

end TabooRegen.Decomp

open MeasureTheory TabooRegen in
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h2 : M.A2) (h3 : M.A3 α) (h4 : M.A4 α) (h7 : M.A7) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) :
    Real.exp (α * t) *
        (M.P {ω | k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧
          ENNReal.ofReal t < M.Γ ω}).toReal =
      ∫ u in Set.Icc 0 t, M.btilde α k B (t - u)
        ∂(SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) (M.Gtilde α)) ∧
    ∀ j : ℕ, ((M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map fun ω => (M.T j ω).toReal).withDensity
        (fun u => ENNReal.ofReal (Real.exp (α * u))) =
      QueueingFundamentals.MG1.convPow (M.Gtilde α) j := by
  exact ⟨TabooRegen.Decomp.decomp_real M hreg h0 α k t ht B hB,
    fun j => TabooRegen.Twist.twisted_law M hreg h0 α j⟩
