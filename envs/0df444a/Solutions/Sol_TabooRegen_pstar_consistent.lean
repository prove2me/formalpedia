-- Prove2me | solution 1 for TabooRegen.pstar_consistent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T15:37:18.855204+00:00
-- url     : https://prove2.me/submissions/84c44c45-ee7f-4776-8ad7-c1e7cd7256ef

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

namespace TabooRegen.PstarC

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

lemma T_ne_top_of_le_Γ {ω : Ω} {n : ℕ} (h : M.T n ω ≤ M.Γ ω) : M.T n ω ≠ ⊤ := by
  intro htop
  have h2 := M.T_top n ω htop
  rw [htop] at h
  exact h2.ne (top_le_iff.1 h)

lemma ae_Q_S0 : ∀ᵐ ω ∂M.Q, M.T 0 ω ≤ M.Γ ω := by
  unfold Model.Q
  exact ProbabilityTheory.ae_cond_mem (measurableSet_le_Γ M 0)

lemma T_add_eq (j : ℕ) (ω : Ω) (n : ℕ) :
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

/-! ### cycle functionals -/

/-- the window map -/
def G (k : ℕ) (p : (ℕ → Path S) × ℝ) : (Fin (2 * k + 1) → Path S) × ℝ :=
  ((fun i : Fin (2 * k + 1) => p.1 i), p.2)

omit [TopologicalSpace S] in
lemma measurable_G [TopologicalSpace S] (k : ℕ) : Measurable (G (S := S) k) :=
  (measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd

/-- the age set of the `k`-th cycle -/
def Dset (A : Set S) (k : ℕ) : Set ((ℕ → Path S) × ℝ) :=
  {p | 0 ≤ p.2 ∧ ENNReal.ofReal p.2 < min (exitTime A (p.1 k).1) (len (p.1 k))}

lemma measurableSet_Dset (hγ : Measurable fun x : Path S => exitTime A x.1) (k : ℕ) :
    MeasurableSet (Dset A k) := by
  have h1 : Measurable fun p : (ℕ → Path S) × ℝ => exitTime A (p.1 k).1 :=
    hγ.comp ((measurable_pi_apply k).comp measurable_fst)
  have h2 : Measurable fun p : (ℕ → Path S) × ℝ => len (p.1 k) :=
    measurable_len.comp ((measurable_pi_apply k).comp measurable_fst)
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (h1.min h2))

/-- the integrand of the straddling-cycle integral -/
noncomputable def dens (A : Set S) (α : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) :
    (ℕ → Path S) × ℝ → ℝ≥0∞ :=
  (Dset A k).indicator (fun p => ed α p.2 * B.indicator (fun _ => (1 : ℝ≥0∞)) (G k p))

lemma measurable_dens (hγ : Measurable fun x : Path S => exitTime A x.1) (α : ℝ) (k : ℕ)
    {B : Set ((Fin (2 * k + 1) → Path S) × ℝ)} (hB : MeasurableSet B) :
    Measurable (dens A α k B) :=
  (((measurable_ed α).comp measurable_snd).mul
    ((measurable_const.indicator hB).comp (measurable_G k))).indicator (measurableSet_Dset hγ k)

/-- the straddling-cycle integral as a functional of the cycles -/
noncomputable def Inn (A : Set S) (α : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ))
    (x : ℕ → Path S) : ℝ≥0∞ :=
  ∫⁻ u, dens A α k B (x, u)

lemma measurable_Inn (hγ : Measurable fun x : Path S => exitTime A x.1) (α : ℝ) (k : ℕ)
    {B : Set ((Fin (2 * k + 1) → Path S) × ℝ)} (hB : MeasurableSet B) :
    Measurable (Inn A α k B) :=
  (measurable_dens hγ α k hB).lintegral_prod_right'

/-- no exit during the first `k` cycles -/
def Good (A : Set S) (k : ℕ) : Set (ℕ → Path S) := {x | ∀ i : Fin k, exitTime A (x i).1 = ⊤}

lemma measurableSet_Good (hγ : Measurable fun x : Path S => exitTime A x.1) (k : ℕ) :
    MeasurableSet (Good A k) := by
  have : Good A k = ⋂ i : Fin k, {x : ℕ → Path S | exitTime A (x i).1 = ⊤} := by
    ext x; simp [Good]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (hγ.comp (measurable_pi_apply (i : ℕ))) (measurableSet_singleton ⊤)

/-- the twisting weight `e^{α(τ₁+⋯+τ_k)} 1{no exit}` -/
noncomputable def Wt (A : Set S) (α : ℝ) (k : ℕ) (x : ℕ → Path S) : ℝ≥0∞ :=
  (Good A k).indicator (fun x => ed α (Tx x k).toReal) x

lemma measurable_Wt (hγ : Measurable fun x : Path S => exitTime A x.1) (α : ℝ) (k : ℕ) :
    Measurable (Wt A α k) :=
  ((measurable_ed α).comp (measurable_Tx k).ennreal_toReal).indicator (measurableSet_Good hγ k)

/-- the `P*` window functional of the cycle sequence -/
noncomputable def Phi (A : Set S) (α : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ))
    (x : ℕ → Path S) : ℝ≥0∞ :=
  Wt A α k x * Inn A α k B x

lemma measurable_Phi (hγ : Measurable fun x : Path S => exitTime A x.1) (α : ℝ) (k : ℕ)
    {B : Set ((Fin (2 * k + 1) → Path S) × ℝ)} (hB : MeasurableSet B) :
    Measurable (Phi A α k B) :=
  (measurable_Wt hγ α k).mul (measurable_Inn hγ α k hB)

lemma le_Γ_iff_good (j : ℕ) (ω : Ω) (hj : M.T j ω ≤ M.Γ ω) (k : ℕ) :
    M.T (j + k) ω ≤ M.Γ ω ↔ ∀ i < k, M.γ (j + 1 + i) ω = ⊤ := by
  induction k with
  | zero => simpa using hj
  | succ k ih =>
    constructor
    · intro h
      have h' : M.T (j + k) ω ≤ M.Γ ω := (M.T_mono (j + k) ω).trans h
      have hk : M.γ (j + k + 1) ω = ⊤ := (le_Γ_succ_iff M h').1 h
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact ih.1 h' i hi
      · subst hi; rw [show j + 1 + i = j + i + 1 by omega]; exact hk
    · intro h
      have h' : M.T (j + k) ω ≤ M.Γ ω := ih.2 fun i hi => h i (by omega)
      have hk := h k (by omega)
      rw [show j + 1 + k = j + k + 1 by omega] at hk
      exact (le_Γ_succ_iff M h').2 hk

lemma mem_Good_cycj (j : ℕ) (ω : Ω) (k : ℕ) :
    cycj M j ω ∈ Good A k ↔ ∀ i < k, M.γ (j + 1 + i) ω = ⊤ :=
  ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

lemma Inn_cycj (α : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (j : ℕ) (ω : Ω) :
    Inn A α k B (cycj M j ω) =
      ∫⁻ x in {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (j + 1 + k) ω) (M.τ (j + 1 + k) ω)},
        ed α x * B.indicator (fun _ => (1 : ℝ≥0∞))
          ((fun i : Fin (2 * k + 1) => M.W (j + 1 + i) ω), x) := by
  have hS : MeasurableSet
      {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (j + 1 + k) ω) (M.τ (j + 1 + k) ω)} :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  unfold Inn dens
  rw [← lintegral_indicator hS]
  refine lintegral_congr fun u => ?_
  have hmem : (cycj M j ω, u) ∈ Dset A k ↔
      u ∈ {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (j + 1 + k) ω) (M.τ (j + 1 + k) ω)} := by
    simp only [Dset, Set.mem_setOf_eq, cycj, len_W]
    exact Iff.rfl
  by_cases hu : u ∈
      {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (j + 1 + k) ω) (M.τ (j + 1 + k) ω)}
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hmem.2 hu)]
    rfl
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h => hu (hmem.1 h))]

/-- on `{T(j) ⩽ Γ}`, the post-`T(j)` window quantity is the functional `Phi` of the cycles after `T(j)` -/
lemma rep (α : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (j : ℕ) (ω : Ω)
    (hj : M.T j ω ≤ M.Γ ω) :
    {ω | M.T (j + k) ω ≤ M.Γ ω}.indicator (fun ω => ed α ((M.T (j + k) ω).toReal - (M.T j ω).toReal) *
      ∫⁻ x in {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (j + 1 + k) ω) (M.τ (j + 1 + k) ω)},
        ed α x * B.indicator (fun _ => (1 : ℝ≥0∞))
          ((fun i : Fin (2 * k + 1) => M.W (j + 1 + i) ω), x)) ω =
      Phi A α k B (cycj M j ω) := by
  unfold Phi Wt
  rw [Inn_cycj]
  by_cases hk : M.T (j + k) ω ≤ M.Γ ω
  · have hg : cycj M j ω ∈ Good A k :=
      (mem_Good_cycj M j ω k).2 ((le_Γ_iff_good M j ω hj k).1 hk)
    rw [Set.indicator_of_mem (show ω ∈ {ω | M.T (j + k) ω ≤ M.Γ ω} from hk),
      Set.indicator_of_mem hg]
    have hfin : M.T (j + k) ω ≠ ⊤ := T_ne_top_of_le_Γ M hk
    have hd : (M.T (j + k) ω).toReal - (M.T j ω).toReal = (Tx (cycj M j ω) k).toReal := by
      rw [T_add_eq M j ω k] at hfin ⊢
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.1 hfin).1 (ENNReal.add_ne_top.1 hfin).2]
      ring
    rw [hd]
  · have hg : cycj M j ω ∉ Good A k := fun h =>
      hk ((le_Γ_iff_good M j ω hj k).2 ((mem_Good_cycj M j ω k).1 h))
    rw [Set.indicator_of_notMem (show ω ∉ {ω | M.T (j + k) ω ≤ M.Γ ω} from hk),
      Set.indicator_of_notMem hg, zero_mul]

lemma cycj_zero (ω : Ω) : cycj M 0 ω = cyc M ω := by
  funext i; simp [cycj, cyc]

/-- `PstarNum k B` is the `Q`-mean of the cycle functional `Phi` -/
lemma U0 (α : ℝ) (k : ℕ) {B : Set ((Fin (2 * k + 1) → Path S) × ℝ)} (hB : MeasurableSet B) :
    M.PstarNum α k B = ∫⁻ x, Phi A α k B x ∂(M.Q.map (cyc M)) := by
  rw [lintegral_map (measurable_Phi M.exit_measurable α k hB) (measurable_cyc' M)]
  unfold Model.PstarNum
  rw [← lintegral_indicator (measurableSet_le_Γ M k)]
  refine lintegral_congr_ae ((ae_Q_S0 M).mono fun ω hω => ?_)
  have h := rep M α k B 0 ω hω
  rw [cycj_zero] at h
  simp only [zero_add] at h
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k] at h
  beta_reduce
  rw [← h]
  rfl

/-- `PstarNum (k+1)` of a `dropOuter` preimage, peeled at the first cycle -/
lemma U1 (α : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) :
    M.PstarNum α (k + 1) ((fun p => (dropOuter k p.1, p.2)) ⁻¹' B) =
      ∫⁻ ω in {ω | M.T 1 ω ≤ M.Γ ω},
        ed α ((M.T 1 ω).toReal - (M.T 0 ω).toReal) * Phi A α k B (cycj M 1 ω) ∂M.Q := by
  unfold Model.PstarNum
  rw [← lintegral_indicator (measurableSet_le_Γ M (k + 1)),
    ← lintegral_indicator (measurableSet_le_Γ M 1)]
  refine lintegral_congr_ae ((ae_Q_S0 M).mono fun ω hω => ?_)
  by_cases h1 : M.T 1 ω ≤ M.Γ ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | M.T 1 ω ≤ M.Γ ω} from h1), ← rep M α k B 1 ω h1]
    rw [show 1 + 1 + k = k + 1 + 1 by omega, show 1 + k = k + 1 by omega]
    by_cases hk : M.T (k + 1) ω ≤ M.Γ ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | M.T (k + 1) ω ≤ M.Γ ω} from hk),
        Set.indicator_of_mem (show ω ∈ {ω | M.T (k + 1) ω ≤ M.Γ ω} from hk)]
      have hsplit : ENNReal.ofReal (Real.exp (α * ((M.T (k + 1) ω).toReal - (M.T 0 ω).toReal))) =
          ed α ((M.T 1 ω).toReal - (M.T 0 ω).toReal) *
            ed α ((M.T (k + 1) ω).toReal - (M.T 1 ω).toReal) := by
        rw [← ed_add]; unfold ed; ring_nf
      rw [hsplit, mul_assoc]
      congr 2
      refine lintegral_congr fun x => ?_
      have e : (dropOuter k (fun i : Fin (2 * (k + 1) + 1) => M.W (1 + (i : ℕ)) ω), x) =
          ((fun i : Fin (2 * k + 1) => M.W (1 + 1 + (i : ℕ)) ω), x) := by
        refine Prod.ext ?_ rfl
        funext i
        simp only [dropOuter]
        congr 1
        omega
      have hw : ((fun p : (Fin (2 * (k + 1) + 1) → Path S) × ℝ => (dropOuter k p.1, p.2)) ⁻¹' B).indicator
          (fun _ => (1 : ℝ≥0∞)) ((fun i : Fin (2 * (k + 1) + 1) => M.W (1 + (i : ℕ)) ω), x) =
          B.indicator (fun _ => (1 : ℝ≥0∞)) ((fun i : Fin (2 * k + 1) => M.W (1 + 1 + (i : ℕ)) ω), x) := by
        rw [← e]; rfl
      show ENNReal.ofReal (Real.exp (α * x)) * _ = ed α x * _
      rw [hw]
      rfl
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | M.T (k + 1) ω ≤ M.Γ ω} from hk),
        Set.indicator_of_notMem (show ω ∉ {ω | M.T (k + 1) ω ≤ M.Γ ω} from hk), mul_zero]
  · have hk : ¬ M.T (k + 1) ω ≤ M.Γ ω := fun h =>
      h1 ((T_mono' M (show 1 ≤ k + 1 by omega)).trans h)
    rw [Set.indicator_of_notMem (show ω ∉ {ω | M.T (k + 1) ω ≤ M.Γ ω} from hk),
      Set.indicator_of_notMem (show ω ∉ {ω | M.T 1 ω ≤ M.Γ ω} from h1)]

/-- Definition 2 at `n = 1`: `(T(0), T(1))` and the cycles after `T(1)` are independent on `{T(1) ⩽ Γ}` -/
lemma prod_law_1 (hreg : M.IsWideSenseTabooRegen) :
    (M.P.restrict {ω | M.T 1 ω ≤ M.Γ ω}).map (fun ω => ((M.T 0 ω, M.T 1 ω), cycj M 1 ω)) =
      ((M.P.restrict {ω | M.T 1 ω ≤ M.Γ ω}).map (fun ω => (M.T 0 ω, M.T 1 ω))).prod
        (M.Q.map (cyc M)) := by
  have := M.isProb
  have := Q_finite' M
  have hT : Measurable fun ω => (M.T 0 ω, M.T 1 ω) := (M.measurable_T 0).prodMk (M.measurable_T 1)
  have hg : Measurable fun ω => ((M.T 0 ω, M.T 1 ω), cycj M 1 ω) :=
    hT.prodMk (measurable_cycj M 1)
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hg (hs.prod ht), Measure.map_apply hT hs,
    Measure.map_apply (measurable_cyc' M) ht, Measure.restrict_apply (hg (hs.prod ht)),
    Measure.restrict_apply (hT hs)]
  have hH : Measurable fun x : Fin (1 + 1) → ℝ≥0∞ => (x 0, x 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have h := hreg 1 t ht ((fun x : Fin (1 + 1) → ℝ≥0∞ => (x 0, x 1)) ⁻¹' s) (hH hs)
  have e1 : {ω | (fun i : ℕ => M.W (1 + 1 + i) ω) ∈ t} ∩
      {ω | (fun i : Fin (1 + 1) => M.T i ω) ∈ (fun x : Fin (1 + 1) → ℝ≥0∞ => (x 0, x 1)) ⁻¹' s} ∩
      {ω | M.T 1 ω ≤ M.Γ ω} =
        (fun ω => ((M.T 0 ω, M.T 1 ω), cycj M 1 ω)) ⁻¹' (s ×ˢ t) ∩ {ω | M.T 1 ω ≤ M.Γ ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, cycj]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one]
    tauto
  have e2 : {ω | (fun i : Fin (1 + 1) => M.T i ω) ∈
      (fun x : Fin (1 + 1) → ℝ≥0∞ => (x 0, x 1)) ⁻¹' s} ∩ {ω | M.T 1 ω ≤ M.Γ ω} =
        (fun ω => (M.T 0 ω, M.T 1 ω)) ⁻¹' s ∩ {ω | M.T 1 ω ≤ M.Γ ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Fin.isValue,
      Fin.val_zero, Fin.val_one]
  rw [e1, e2] at h
  exact h

lemma restrict_Q_E1 (f : Ω → ℝ≥0∞) :
    ∫⁻ ω in {ω | M.T 1 ω ≤ M.Γ ω}, f ω ∂M.Q =
      (M.P {ω | M.T 0 ω ≤ M.Γ ω})⁻¹ * ∫⁻ ω in {ω | M.T 1 ω ≤ M.Γ ω}, f ω ∂M.P := by
  unfold Model.Q ProbabilityTheory.cond
  rw [Measure.restrict_smul, Measure.restrict_restrict (measurableSet_le_Γ M 1),
    lintegral_smul_measure]
  have hsub : {ω | M.T 1 ω ≤ M.Γ ω} ∩ {ω | M.T 0 ω ≤ M.Γ ω} = {ω | M.T 1 ω ≤ M.Γ ω} :=
    Set.inter_eq_left.2 fun ω (h : M.T 1 ω ≤ M.Γ ω) => (M.T_mono 0 ω).trans h
  rw [hsub]
  rfl

lemma split1 (hreg : M.IsWideSenseTabooRegen) (g : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞) (hg : Measurable g)
    (F : (ℕ → Path S) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω in {ω | M.T 1 ω ≤ M.Γ ω}, g (M.T 0 ω, M.T 1 ω) * F (cycj M 1 ω) ∂M.Q =
      (∫⁻ ω in {ω | M.T 1 ω ≤ M.Γ ω}, g (M.T 0 ω, M.T 1 ω) ∂M.Q) *
        ∫⁻ x, F x ∂(M.Q.map (cyc M)) := by
  have := M.isProb
  have := Q_finite' M
  have hT : Measurable fun ω => (M.T 0 ω, M.T 1 ω) := (M.measurable_T 0).prodMk (M.measurable_T 1)
  have hpair : Measurable fun ω => ((M.T 0 ω, M.T 1 ω), cycj M 1 ω) :=
    hT.prodMk (measurable_cycj M 1)
  have hP : ∫⁻ ω in {ω | M.T 1 ω ≤ M.Γ ω}, g (M.T 0 ω, M.T 1 ω) * F (cycj M 1 ω) ∂M.P =
      (∫⁻ ω in {ω | M.T 1 ω ≤ M.Γ ω}, g (M.T 0 ω, M.T 1 ω) ∂M.P) *
        ∫⁻ x, F x ∂(M.Q.map (cyc M)) := by
    have h := lintegral_map (f := fun p : (ℝ≥0∞ × ℝ≥0∞) × (ℕ → Path S) => g p.1 * F p.2)
      ((hg.comp measurable_fst).mul (hF.comp measurable_snd)) hpair
      (μ := M.P.restrict {ω | M.T 1 ω ≤ M.Γ ω})
    rw [prod_law_1 M hreg, lintegral_prod_mul hg.aemeasurable hF.aemeasurable,
      lintegral_map hg hT] at h
    exact h.symm
  rw [restrict_Q_E1, restrict_Q_E1, hP, mul_assoc]

lemma Q_noExit_pos {α : ℝ} (h1 : M.A1 α) : 0 < M.Q (M.NoExit 1) := by
  refine pos_iff_ne_zero.2 fun h => ?_
  have h2 := h1.2
  unfold Model.cycleMGF at h2
  rw [Measure.restrict_eq_zero.2 h, lintegral_zero_measure] at h2
  exact zero_ne_one h2

lemma mgf_one {α : ℝ} (h1 : M.A1 α) :
    ∫⁻ ω in {ω | M.T 1 ω ≤ M.Γ ω}, ed α ((M.T 1 ω).toReal - (M.T 0 ω).toReal) ∂M.Q = 1 := by
  rw [← h1.2]
  unfold Model.cycleMGF
  rw [← lintegral_indicator (measurableSet_le_Γ M 1),
    ← lintegral_indicator (measurableSet_NoExit M 1)]
  refine lintegral_congr_ae ((ae_Q_S0 M).mono fun ω hω => ?_)
  have hiff : M.T 1 ω ≤ M.Γ ω ↔ ω ∈ M.NoExit 1 := le_Γ_succ_iff M hω
  by_cases h : M.T 1 ω ≤ M.Γ ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | M.T 1 ω ≤ M.Γ ω} from h),
      Set.indicator_of_mem (hiff.1 h)]
    have hτ : M.τ 1 ω = M.T 1 ω - M.T 0 ω := by simp [Model.τ, Model.Tm, prevTime]
    rw [hτ, ENNReal.toReal_sub_of_le (M.T_mono 0 ω) (T_ne_top_of_le_Γ M h)]
    rfl
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | M.T 1 ω ≤ M.Γ ω} from h),
      Set.indicator_of_notMem (fun hh => h (hiff.2 hh))]

theorem consist (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (k : ℕ)
    (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) :
    M.PstarNum α (k + 1) ((fun p => (dropOuter k p.1, p.2)) ⁻¹' B) = M.PstarNum α k B := by
  have hg : Measurable fun p : ℝ≥0∞ × ℝ≥0∞ => ed α (p.2.toReal - p.1.toReal) :=
    (measurable_ed α).comp (measurable_snd.ennreal_toReal.sub measurable_fst.ennreal_toReal)
  have hs := split1 M hreg _ hg (Phi A α k B) (measurable_Phi M.exit_measurable α k hB)
  dsimp only at hs
  rw [U1, hs, mgf_one M h1, one_mul, U0 M α k hB]

lemma pnum_zero_univ {α : ℝ} : M.PstarNum α 0 Set.univ = M.cycleWeight α := by
  unfold Model.PstarNum Model.cycleWeight
  rw [Measure.restrict_eq_self_of_ae_mem (s := {ω | M.T 0 ω ≤ M.Γ ω}) (ae_Q_S0 M)]
  refine lintegral_congr fun ω => ?_
  simp only [sub_self, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul, Set.indicator_univ,
    mul_one, zero_add]

lemma pnum_univ (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (k : ℕ) :
    M.PstarNum α k Set.univ = M.cycleWeight α := by
  induction k with
  | zero => exact pnum_zero_univ M
  | succ k ih =>
    have h := consist M hreg h1 k Set.univ MeasurableSet.univ
    rw [Set.preimage_univ] at h
    rw [h, ih]

lemma ed_ge_one {α u : ℝ} (hα : 0 ≤ α) (hu : 0 ≤ u) : 1 ≤ ENNReal.ofReal (Real.exp (α * u)) :=
  ENNReal.one_le_ofReal.2 (Real.one_le_exp (mul_nonneg hα hu))

lemma cw_ne_zero {α : ℝ} (h1 : M.A1 α) : M.cycleWeight α ≠ 0 := by
  have hm : Measurable fun ω => ENNReal.ofReal (M.τ 1 ω).toReal :=
    ENNReal.measurable_ofReal.comp (measurable_τ' M 1).ennreal_toReal
  have hpos : 0 < ∫⁻ ω in M.NoExit 1, ENNReal.ofReal (M.τ 1 ω).toReal ∂M.Q := by
    rw [lintegral_pos_iff_support hm, Measure.restrict_apply' (measurableSet_NoExit M 1)]
    refine lt_of_lt_of_le (Q_noExit_pos M h1) (measure_mono_ae ?_)
    filter_upwards [ae_Q_S0 M] with ω hω
    intro hN
    refine ⟨?_, hN⟩
    have hT0 : M.T 0 ω ≠ ⊤ := T_ne_top_of_le_Γ M hω
    have hT1 : M.T 1 ω ≠ ⊤ := T_ne_top_of_le_Γ M (le_Γ_succ M hω hN)
    have hlt : M.T 0 ω < M.T 1 ω := M.T_strict 0 ω (lt_top_iff_ne_top.2 hT0)
    have hτ : M.τ 1 ω = M.T 1 ω - M.T 0 ω := by simp [Model.τ, Model.Tm, prevTime]
    have hpos' : 0 < (M.τ 1 ω).toReal := by
      rw [hτ]
      exact ENNReal.toReal_pos (tsub_pos_iff_lt.2 hlt).ne' (ENNReal.sub_ne_top hT1)
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos'
  refine (lt_of_lt_of_le hpos ?_).ne'
  unfold Model.cycleWeight
  rw [← lintegral_indicator (measurableSet_NoExit M 1)]
  refine lintegral_mono_ae ((ae_Q_S0 M).mono fun ω hω => ?_)
  by_cases hN : ω ∈ M.NoExit 1
  · rw [Set.indicator_of_mem hN]
    have hT1 : M.T 1 ω ≠ ⊤ := T_ne_top_of_le_Γ M (le_Γ_succ M hω hN)
    have hτ : M.τ 1 ω = M.T 1 ω - M.T 0 ω := by simp [Model.τ, Model.Tm, prevTime]
    have hτf : M.τ 1 ω ≠ ⊤ := by rw [hτ]; exact ENNReal.sub_ne_top hT1
    have hsub : Set.Ico 0 (M.τ 1 ω).toReal ⊆
        {u : ℝ | 0 ≤ u ∧ ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)} := by
      intro u hu
      refine ⟨hu.1, ?_⟩
      have hγ : M.γ 1 ω = ⊤ := hN
      rw [hγ, min_eq_right le_top]
      exact (ENNReal.ofReal_lt_iff_lt_toReal hu.1 hτf).2 hu.2
    calc ENNReal.ofReal (M.τ 1 ω).toReal = ∫⁻ u in Set.Ico 0 (M.τ 1 ω).toReal, 1 := by
          rw [setLIntegral_one, Real.volume_Ico, sub_zero]
      _ ≤ ∫⁻ u in Set.Ico 0 (M.τ 1 ω).toReal, ENNReal.ofReal (Real.exp (α * u)) :=
          setLIntegral_mono (measurable_ed α) fun u hu => ed_ge_one h1.1 hu.1
      _ ≤ ∫⁻ u in {u : ℝ | 0 ≤ u ∧ ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)},
            ENNReal.ofReal (Real.exp (α * u)) := lintegral_mono_set hsub
  · rw [Set.indicator_of_notMem hN]
    simp

lemma cw_ne_top {α : ℝ} (h4 : M.A4 α) : M.cycleWeight α ≠ ⊤ := by
  obtain ⟨h, -, hhi, hb⟩ := h4
  have := Q_finite' M
  set E : Set (Ω × ℝ) := {p | 0 ≤ p.2 ∧ ENNReal.ofReal p.2 < min (M.γ 1 p.1) (M.τ 1 p.1)} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
        (((M.exit_measurable.comp (M.measurable_W 1)).comp measurable_fst).min
          ((measurable_τ' M 1).comp measurable_fst)))
  set f : Ω × ℝ → ℝ≥0∞ := E.indicator (fun p => ed α p.2) with hf
  have hfm : Measurable f := ((measurable_ed α).comp measurable_snd).indicator hEm
  have e1 : M.cycleWeight α = ∫⁻ ω, (∫⁻ u, f (ω, u) ∂volume) ∂M.Q := by
    unfold Model.cycleWeight
    refine lintegral_congr fun ω => ?_
    have hS : MeasurableSet {u : ℝ | 0 ≤ u ∧ ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)} :=
      (measurableSet_le measurable_const measurable_id).inter
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
    rw [← lintegral_indicator hS]
    rfl
  rw [e1, lintegral_lintegral_swap (f := fun ω u => f (ω, u)) hfm.aemeasurable]
  refine ne_top_of_le_ne_top (hhi.lintegral_lt_top).ne ?_
  rw [← lintegral_indicator measurableSet_Ici]
  refine lintegral_mono fun u => ?_
  by_cases hu : 0 ≤ u
  · rw [Set.indicator_of_mem (show u ∈ Set.Ici (0 : ℝ) from hu)]
    have hSm : MeasurableSet {ω | ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)} :=
      measurableSet_lt measurable_const
        ((M.exit_measurable.comp (M.measurable_W 1)).min (measurable_τ' M 1))
    have hI : ∫⁻ ω, f (ω, u) ∂M.Q =
        ed α u * M.Q {ω | ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)} := by
      rw [← lintegral_indicator_const hSm]
      refine lintegral_congr fun ω => ?_
      by_cases hω : ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)
      · rw [Set.indicator_of_mem (show ω ∈ {ω | ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)} from hω),
          hf, Set.indicator_of_mem (show (ω, u) ∈ E from ⟨hu, hω⟩)]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)} from hω),
          hf, Set.indicator_of_notMem (show (ω, u) ∉ E from fun h => hω h.2)]
    rw [hI]
    calc ed α u * M.Q {ω | ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)} =
        ENNReal.ofReal (Real.exp (α * u) *
          (M.Q {ω | ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)}).toReal) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (measure_ne_top _ _)]
          rfl
      _ ≤ ENNReal.ofReal (h u) := ENNReal.ofReal_le_ofReal (hb u hu)
  · have h0 : (fun ω => f (ω, u)) = fun _ => 0 := by
      funext ω
      rw [hf, Set.indicator_of_notMem (show (ω, u) ∉ E from fun h => hu h.1)]
    rw [h0, lintegral_zero]
    simp

lemma ind_pt (α : ℝ) (k : ℕ) (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (x : ℕ → Path S) (u : ℝ) :
    (G k ⁻¹' B).indicator (fun p => Wt A α k p.1 * (Dset A k).indicator (fun p => ed α p.2) p) (x, u) =
      Wt A α k x * dens A α k B (x, u) := by
  unfold dens
  by_cases hG : G k (x, u) ∈ B <;> by_cases hD : (x, u) ∈ Dset A k <;>
    simp [Set.indicator, hG, hD, Set.mem_preimage]

theorem main (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (h4 : M.A4 α) (k : ℕ) :
    (∃ μ : Measure ((Fin (2 * k + 1) → Path S) × ℝ), IsProbabilityMeasure μ ∧
        ∀ B, MeasurableSet B → μ B = M.PstarWindow α k B) ∧
      ∀ B : Set ((Fin (2 * k + 1) → Path S) × ℝ), MeasurableSet B →
        M.PstarWindow α (k + 1) ((fun p => (dropOuter k p.1, p.2)) ⁻¹' B) =
          M.PstarWindow α k B := by
  have := Q_finite' M
  have hγ := M.exit_measurable
  refine ⟨?_, fun B hB => ?_⟩
  · set ν : Measure ((ℕ → Path S) × ℝ) := (M.Q.map (cyc M)).prod (volume : Measure ℝ) with hν
    set d : (ℕ → Path S) × ℝ → ℝ≥0∞ := fun p => Wt A α k p.1 * (Dset A k).indicator (fun p => ed α p.2) p
      with hd
    have hdm : Measurable d :=
      ((measurable_Wt hγ α k).comp measurable_fst).mul
        (((measurable_ed α).comp measurable_snd).indicator (measurableSet_Dset hγ k))
    set μ : Measure ((Fin (2 * k + 1) → Path S) × ℝ) :=
      (M.cycleWeight α)⁻¹ • (ν.withDensity d).map (G k) with hμ
    have hval : ∀ B, MeasurableSet B → μ B = M.PstarWindow α k B := by
      intro B hB
      rw [hμ, Measure.smul_apply, Measure.map_apply (measurable_G k) hB,
        withDensity_apply _ ((measurable_G k) hB), ← lintegral_indicator ((measurable_G k) hB), hν,
        lintegral_prod _ ((hdm.indicator ((measurable_G k) hB)).aemeasurable)]
      have hpt : ∀ x : ℕ → Path S, ∫⁻ u, (G k ⁻¹' B).indicator d (x, u) = Phi A α k B x := by
        intro x
        unfold Phi Inn
        rw [← lintegral_const_mul (f := fun u => dens A α k B (x, u)) (Wt A α k x)
          ((measurable_dens hγ α k hB).comp measurable_prodMk_left)]
        exact lintegral_congr fun u => ind_pt α k B x u
      simp_rw [hpt]
      rw [← U0 M α k hB, Model.PstarWindow, smul_eq_mul, ENNReal.div_eq_inv_mul]
    refine ⟨μ, ⟨?_⟩, hval⟩
    rw [hval Set.univ MeasurableSet.univ, Model.PstarWindow, pnum_univ M hreg h1 k,
      ENNReal.div_self (cw_ne_zero M h1) (cw_ne_top M h4)]
  · unfold Model.PstarWindow
    rw [consist M hreg h1 k B hB]

end TabooRegen.PstarC

open MeasureTheory TabooRegen in
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (h4 : M.A4 α) (k : ℕ) :
    (∃ μ : Measure ((Fin (2 * k + 1) → Path S) × ℝ), IsProbabilityMeasure μ ∧
        ∀ B, MeasurableSet B → μ B = M.PstarWindow α k B) ∧
      ∀ B : Set ((Fin (2 * k + 1) → Path S) × ℝ), MeasurableSet B →
        M.PstarWindow α (k + 1) ((fun p => (dropOuter k p.1, p.2)) ⁻¹' B) =
          M.PstarWindow α k B := by
  exact TabooRegen.PstarC.main M hreg h1 h4 k
