-- Prove2me | solution 1 for TabooRegen.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T17:14:44.1243+00:00
-- url     : https://prove2.me/submissions/227a877b-3168-427e-9ce1-c82619f5bfa6

import Mathlib
import Definitions.Def_TabooRegen_Window
import Theorems.Thm_TabooRegen_delay_shift
import Theorems.Thm_TabooRegen_proposition_2

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

namespace TabooRegen.Prop3

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen TabooRegen.Twist

section General

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

lemma T_monotone (ω : Ω) : Monotone fun n => M.T n ω :=
  monotone_nat_of_le_succ fun n => M.T_mono n ω

lemma lt_strad_iff (K : ℕ) (u : ℝ) (ω : Ω) :
    K < M.strad u ω ↔ M.T K ω ≤ ENNReal.ofReal u ∧ ∃ n, ENNReal.ofReal u < M.T n ω := by
  unfold Model.strad
  constructor
  · intro h
    have hne : {n : ℕ | ENNReal.ofReal u < M.T n ω}.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, Nat.sInf_empty] at h
      exact Nat.not_lt_zero _ h
    refine ⟨?_, hne⟩
    by_contra hK
    push_neg at hK
    exact absurd (Nat.sInf_le hK) (not_le.mpr h)
  · rintro ⟨hK, hne⟩
    have hmem : ENNReal.ofReal u < M.T (sInf {n : ℕ | ENNReal.ofReal u < M.T n ω}) ω :=
      Nat.sInf_mem hne
    by_contra h
    push_neg at h
    have := T_monotone M ω h
    exact absurd hK (not_le.mpr (lt_of_lt_of_le hmem this))

lemma Q_eq_zero (h : M.P {ω | M.T 0 ω ≤ M.Γ ω} = 0) : M.Q = 0 := by
  unfold Model.Q
  rw [ProbabilityTheory.cond, Measure.restrict_eq_zero.mpr h, smul_zero]

lemma P_S0_ne_zero {α : ℝ} (h1 : M.A1 α) : M.P {ω | M.T 0 ω ≤ M.Γ ω} ≠ 0 := by
  intro h
  have h2 := h1.2
  unfold Model.cycleMGF at h2
  rw [Q_eq_zero M h] at h2
  simp at h2

lemma Q_noExit_ne_zero {α : ℝ} (h1 : M.A1 α) : M.Q (M.NoExit 1) ≠ 0 := by
  intro h
  have h2 := h1.2
  unfold Model.cycleMGF at h2
  rw [Measure.restrict_eq_zero.mpr h] at h2
  simp at h2

lemma ed_le_one {u : ℝ} (hu : 0 ≤ u) : ed (-1) u ≤ 1 := by
  unfold ed
  rw [ENNReal.ofReal_le_one]
  exact Real.exp_le_one_iff.mpr (by linarith)

lemma K_const (α : ℝ) (j : ℕ) (c : ℝ≥0∞) :
    K M α j (fun _ => c) = c * K M α j (fun _ => 1) := by
  unfold K
  simp only [mul_one]
  have hm : Measurable fun ω => ed α (M.T j ω).toReal :=
    (measurable_ed α).comp (M.measurable_T j).ennreal_toReal
  rw [lintegral_mul_const _ hm, mul_comm]

/-- K4: A5 gives a finite `E[e^{α T(0)}; T(0) ⩽ Γ]` (the cycle `W₁` stays in `A` with positive
`Q`-probability, and on that event `T(0) < Γ`). -/
lemma lint_T0_lt_top (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (h5 : M.A5 α) :
    ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, ed α (M.T 0 ω).toReal ∂M.P < ⊤ := by
  have := M.isProb
  have := Q_finite' M
  have hgm : Measurable fun a : ℝ≥0∞ => ed α a.toReal :=
    (measurable_ed α).comp ENNReal.measurable_toReal
  set Z : Set (ℕ → Path S) := {x | exitTime A (x 0).1 = ⊤} with hZ
  have hZm : MeasurableSet Z :=
    (M.exit_measurable.comp (measurable_pi_apply 0)) (measurableSet_singleton ⊤)
  have hInd : Measurable (Z.indicator (1 : (ℕ → Path S) → ℝ≥0∞)) := measurable_one.indicator hZm
  have hmap : Measurable fun ω => (M.T 0 ω, cycj M 0 ω) :=
    (M.measurable_T 0).prodMk (measurable_cycj M 0)
  have hF : Measurable fun p : ℝ≥0∞ × (ℕ → Path S) => ed α p.1.toReal * Z.indicator 1 p.2 :=
    (hgm.comp measurable_fst).mul (hInd.comp measurable_snd)
  have hprod : ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, ed α (M.T 0 ω).toReal * Z.indicator 1 (cycj M 0 ω) ∂M.P =
      (∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, ed α (M.T 0 ω).toReal ∂M.P) * M.Q (M.NoExit 1) := by
    have e := lintegral_map (μ := M.P.restrict {ω | M.T 0 ω ≤ M.Γ ω}) hF hmap
    dsimp only at e
    rw [← e, prod_law_j M hreg 0, lintegral_prod_mul hgm.aemeasurable hInd.aemeasurable,
      lintegral_map hgm (M.measurable_T 0), lintegral_indicator_one hZm,
      Measure.map_apply (measurable_cyc' M) hZm]
    rfl
  have hmeasLt : MeasurableSet {ω | M.T 0 ω < M.Γ ω} :=
    measurableSet_lt (M.measurable_T 0) (measurable_Γ M)
  have hle : ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, ed α (M.T 0 ω).toReal * Z.indicator 1 (cycj M 0 ω) ∂M.P ≤
      ∫⁻ ω in {ω | M.T 0 ω < M.Γ ω}, ed α (M.T 0 ω).toReal ∂M.P := by
    calc _ ≤ ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω},
          {ω | M.T 0 ω < M.Γ ω}.indicator (fun ω => ed α (M.T 0 ω).toReal) ω ∂M.P := by
          refine setLIntegral_mono ((hgm.comp (M.measurable_T 0)).indicator hmeasLt) fun ω hω => ?_
          by_cases hz : cycj M 0 ω ∈ Z
          · have hγ1 : M.γ (0 + 1) ω = ⊤ := hz
            have hT1 := le_Γ_succ M hω hγ1
            have hlt : M.T 0 ω < M.Γ ω :=
              lt_of_lt_of_le (M.T_strict 0 ω (lt_top_iff_ne_top.2 (T0_ne_top M hω))) hT1
            rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show ω ∈ {ω | M.T 0 ω < M.Γ ω} from hlt)]
            simp
          · rw [Set.indicator_of_notMem hz]; simp
      _ ≤ ∫⁻ ω, {ω | M.T 0 ω < M.Γ ω}.indicator (fun ω => ed α (M.T 0 ω).toReal) ω ∂M.P :=
          setLIntegral_le_lintegral _ _
      _ = _ := lintegral_indicator hmeasLt _
  have h5' : ∫⁻ ω in {ω | M.T 0 ω < M.Γ ω}, ed α (M.T 0 ω).toReal ∂M.P < ⊤ := h5
  have key := hprod ▸ (hle.trans_lt h5')
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.top_mul (Q_noExit_ne_zero M h1)] at key
  exact lt_irrefl _ key

/-- K3: the explosion event is null (any model with Definition 2; Laplace transform at `-1`). -/
lemma explosion_null' (hreg : M.IsWideSenseTabooRegen) (t : ℝ) :
    M.P {ω | ∀ n, M.T n ω ≤ ENNReal.ofReal t ∧ M.T n ω ≤ M.Γ ω} = 0 := by
  have := M.isProb
  have := Q_finite' M
  set ρ : ℝ≥0∞ := ∫⁻ _, (1 : ℝ≥0∞) ∂(M.Gtilde (-1)) with hρ
  have hK1 : ∀ n, K M (-1) n (fun _ => 1) ≤ ρ ^ n := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      unfold K
      calc _ ≤ ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, 1 ∂M.P := lintegral_mono fun ω => by
              rw [mul_one]; exact ed_le_one ENNReal.toReal_nonneg
        _ ≤ 1 := by rw [setLIntegral_one]; exact prob_le_one
    | succ n ih =>
      rw [K_succ M hreg (-1) n measurable_const]
      show K M (-1) n (fun _ => ρ) ≤ ρ ^ (n + 1)
      rw [K_const, pow_succ, mul_comm]
      gcongr
  have hρ1 : ρ < 1 := by
    rw [hρ, lintegral_Gtilde M (-1) measurable_const]
    by_cases hQ : M.Q.restrict (M.NoExit 1) = 0
    · rw [hQ]; simp
    · have hPS : M.P {ω | M.T 0 ω ≤ M.Γ ω} ≠ 0 := by
        intro h; apply hQ; rw [Q_eq_zero M h]; simp
      haveI : IsProbabilityMeasure M.Q := ProbabilityTheory.cond_isProbabilityMeasure hPS
      have hle1 : ∀ ω, ed (-1) (M.τ 1 ω).toReal * 1 ≤ 1 := fun ω => by
        rw [mul_one]; exact ed_le_one ENNReal.toReal_nonneg
      calc _ < ∫⁻ ω in M.NoExit 1, 1 ∂M.Q := by
            refine lintegral_strict_mono hQ aemeasurable_const ?_ ?_
            · exact (lt_of_le_of_lt (lintegral_mono hle1)
                (by rw [setLIntegral_one]; exact measure_lt_top _ _)).ne
            · have hS0 : ∀ᵐ ω ∂M.Q, ω ∈ {ω | M.T 0 ω ≤ M.Γ ω} :=
                ProbabilityTheory.ae_cond_mem (measurableSet_le_Γ M 0)
              filter_upwards [ae_restrict_of_ae hS0, ae_restrict_mem (measurableSet_NoExit M 1)]
                with ω hω hN
              have h0f := T0_ne_top M hω
              have h01 : M.T 0 ω < M.T (0 + 1) ω := M.T_strict 0 ω (lt_top_iff_ne_top.2 h0f)
              have h1Γ : M.T (0 + 1) ω ≤ M.Γ ω := le_Γ_succ M hω hN
              have h1f : M.T 1 ω ≠ ⊤ := fun h => by
                have h2 := M.T_top 1 ω h
                have h3 : M.T 1 ω ≤ M.Γ ω := h1Γ
                rw [h] at h3
                exact absurd (top_le_iff.1 h3) (ne_of_lt (by simpa [Model.Γ] using h2))
              have hτ : (M.τ 1 ω).toReal = (M.T 1 ω).toReal - (M.T 0 ω).toReal := by
                have : M.τ 1 ω = M.T 1 ω - M.T 0 ω := by simp [Model.τ, Model.Tm, prevTime]
                rw [this, ENNReal.toReal_sub_of_le h01.le h1f]
              have hpos : 0 < (M.τ 1 ω).toReal := by
                rw [hτ]; linarith [(ENNReal.toReal_lt_toReal h0f h1f).2 h01]
              rw [mul_one]; unfold ed
              rw [ENNReal.ofReal_lt_one]
              exact Real.exp_lt_one_iff.mpr (by linarith)
        _ = M.Q (M.NoExit 1) := setLIntegral_one _
        _ ≤ 1 := prob_le_one
  set t' := max t 0 with ht'
  have hDm : MeasurableSet {ω | ∀ n, M.T n ω ≤ ENNReal.ofReal t ∧ M.T n ω ≤ M.Γ ω} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun n => (measurableSet_le (M.measurable_T n)
      (measurable_const : Measurable fun _ : Ω => ENNReal.ofReal t)).inter
      (measurableSet_le (M.measurable_T n) (measurable_Γ M))
  have hmK : ∀ n, Measurable fun ω => ed (-1) (M.T n ω).toReal * 1 := fun n =>
    ((measurable_ed (-1)).comp (M.measurable_T n).ennreal_toReal).mul measurable_const
  have hbound : ∀ n, M.P {ω | ∀ n, M.T n ω ≤ ENNReal.ofReal t ∧ M.T n ω ≤ M.Γ ω} ≤
      ENNReal.ofReal (Real.exp t') * ρ ^ n := by
    intro n
    calc M.P {ω | ∀ n, M.T n ω ≤ ENNReal.ofReal t ∧ M.T n ω ≤ M.Γ ω}
        = ∫⁻ ω in {ω | ∀ n, M.T n ω ≤ ENNReal.ofReal t ∧ M.T n ω ≤ M.Γ ω}, 1 ∂M.P :=
          (setLIntegral_one _).symm
      _ ≤ ∫⁻ ω in {ω | ∀ n, M.T n ω ≤ ENNReal.ofReal t ∧ M.T n ω ≤ M.Γ ω},
            ENNReal.ofReal (Real.exp t') * (ed (-1) (M.T n ω).toReal * 1) ∂M.P := by
          refine setLIntegral_mono (measurable_const.mul (hmK n)) fun ω hω => ?_
          have hx : (M.T n ω).toReal ≤ t' :=
            ENNReal.toReal_le_of_le_ofReal (le_max_right t 0)
              ((hω n).1.trans (ENNReal.ofReal_le_ofReal (le_max_left t 0)))
          rw [mul_one]; unfold ed
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ENNReal.one_le_ofReal]
          exact Real.one_le_exp (by linarith)
      _ ≤ ∫⁻ ω in {ω | M.T n ω ≤ M.Γ ω},
            ENNReal.ofReal (Real.exp t') * (ed (-1) (M.T n ω).toReal * 1) ∂M.P :=
          lintegral_mono_set fun ω hω => (hω n).2
      _ = ENNReal.ofReal (Real.exp t') * K M (-1) n (fun _ => 1) := by
          rw [lintegral_const_mul _ (hmK n)]; rfl
      _ ≤ _ := by gcongr; exact hK1 n
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp t') * ρ ^ n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ1)
      (Or.inr (ENNReal.ofReal_ne_top (r := Real.exp t')))
    rwa [mul_zero] at this
  exact le_antisymm (ge_of_tendsto' hlim hbound) bot_le

/-- off the null explosion event, `0 < N(t)` with `t < Γ` is `T(0) ⩽ t < Γ` -/
lemma P_strad_eq (hreg : M.IsWideSenseTabooRegen) (t : ℝ) :
    M.P {ω | 0 < M.strad t ω ∧ ENNReal.ofReal t < M.Γ ω} =
      M.P {ω | M.T 0 ω ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < M.Γ ω} := by
  refine le_antisymm (measure_mono fun ω hω => ⟨((lt_strad_iff M 0 t ω).1 hω.1).1, hω.2⟩) ?_
  calc M.P {ω | M.T 0 ω ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < M.Γ ω}
      ≤ M.P ({ω | 0 < M.strad t ω ∧ ENNReal.ofReal t < M.Γ ω} ∪
          {ω | ∀ n, M.T n ω ≤ ENNReal.ofReal t ∧ M.T n ω ≤ M.Γ ω}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hex : ∃ n, ENNReal.ofReal t < M.T n ω
        · exact Or.inl ⟨(lt_strad_iff M 0 t ω).2 ⟨hω.1, hex⟩, hω.2⟩
        · push_neg at hex
          exact Or.inr fun n => ⟨hex n, (hex n).trans hω.2.le⟩
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [explosion_null' M hreg t, add_zero]

end General

/-- Proposition 3 from Proposition 2 for the non-delayed version `M'` and the delay reduction. -/
theorem prop3_core {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
    {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (h5 : M.A5 α) (h6 : M.A6 α)
    (M' : Model S A {ω // M.T 0 ω ≤ M.Γ ω}) (hreg' : M'.IsWideSenseTabooRegen)
    (h0' : ∀ ω, M'.T 0 ω = 0) (hc1 : 0 < M'.c1 α)
    (hlim : Tendsto (fun t : ℝ => Real.exp (α * t) * (M'.P {ω | ENNReal.ofReal t < M'.Γ ω}).toReal)
      atTop (𝓝 (M'.c1 α)))
    (hrate : M'.rate α = M.rate α) (hcw : M'.cycleWeight α = M.cycleWeight α)
    (hDS : ∀ t : ℝ, 0 ≤ t →
      M.P {ω | 0 < M.strad t ω ∧ (M.win 0 t ω, M.age t ω) ∈
          (Set.univ : Set ((Fin (2 * 0 + 1) → Path S) × ℝ)) ∧ ENNReal.ofReal t < M.Γ ω} =
        ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, (if M.T 0 ω ≤ ENNReal.ofReal t then
          M'.P {ω' | 0 < M'.strad (t - (M.T 0 ω).toReal) ω' ∧
            (M'.win 0 (t - (M.T 0 ω).toReal) ω', M'.age (t - (M.T 0 ω).toReal) ω') ∈
              (Set.univ : Set ((Fin (2 * 0 + 1) → Path S) × ℝ)) ∧
            ENNReal.ofReal (t - (M.T 0 ω).toReal) < M'.Γ ω'} else 0) ∂M.P) :
    0 < M.c2 α ∧
      Tendsto (fun t : ℝ => Real.exp (α * t) * (M.P {ω | ENNReal.ofReal t < M.Γ ω}).toReal)
        atTop (𝓝 (M.c2 α)) := by
  haveI := M.isProb
  haveI := M'.isProb
  have hc1eq : M'.c1 α = M.c1 α := by
    unfold Model.c1
    unfold Model.rate at hrate
    rw [hcw, inv_inj.mp hrate]
  rw [hc1eq] at hc1 hlim
  obtain ⟨L, hLdef⟩ : ∃ L, L = ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, ed α (M.T 0 ω).toReal ∂M.P :=
    ⟨_, rfl⟩
  have hLtop : L < ⊤ := hLdef ▸ lint_T0_lt_top M hreg h1 h5
  have hPS := P_S0_ne_zero M h1
  have hS0m : MeasurableSet {ω | M.T 0 ω ≤ M.Γ ω} := measurableSet_le_Γ M 0
  have hLpos : 0 < L := by
    rw [hLdef]
    calc (0 : ℝ≥0∞) < M.P {ω | M.T 0 ω ≤ M.Γ ω} := pos_iff_ne_zero.2 hPS
      _ = ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, 1 ∂M.P := (setLIntegral_one _).symm
      _ ≤ _ := lintegral_mono fun ω => by
          unfold ed
          exact ENNReal.one_le_ofReal.2 (Real.one_le_exp (mul_nonneg h1.1 ENNReal.toReal_nonneg))
  have hc2 : M.c2 α = L.toReal * M.c1 α := by rw [hLdef]; rfl
  refine ⟨by rw [hc2]; exact mul_pos (ENNReal.toReal_pos hLpos.ne' hLtop.ne) hc1, ?_⟩
  set c1 := M.c1 α with hc1def
  set φ : ℝ → ℝ := fun s => (M'.P {ω' | ENNReal.ofReal s < M'.Γ ω'}).toReal with hφ
  set f : ℝ → ℝ := fun s => Real.exp (α * s) * φ s with hf
  have hflim : Tendsto f atTop (𝓝 c1) := hlim
  have hφmeas : Measurable φ := by
    apply Antitone.measurable
    intro s s' hss
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun ω' hω' => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hss) hω')
  have hfmeas : Measurable f :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hφmeas
  obtain ⟨C, hC⟩ : ∃ C, ∀ s, f s ≤ C := by
    obtain ⟨R, hR⟩ := eventually_atTop.1 (hflim.eventually (eventually_le_nhds (lt_add_one c1)))
    refine ⟨max (Real.exp (α * R)) (c1 + 1), fun s => ?_⟩
    by_cases hs : R ≤ s
    · exact (hR s hs).trans (le_max_right _ _)
    · push_neg at hs
      refine le_trans ?_ (le_max_left _ _)
      have hφ1 : φ s ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
      have hφ0 : 0 ≤ φ s := ENNReal.toReal_nonneg
      have he : Real.exp (α * s) ≤ Real.exp (α * R) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.le h1.1)
      calc f s = Real.exp (α * s) * φ s := rfl
        _ ≤ Real.exp (α * R) * 1 := mul_le_mul he hφ1 hφ0 (Real.exp_pos _).le
        _ = _ := mul_one _
  set G : ℝ → Ω → ℝ≥0∞ := fun t ω => if M.T 0 ω ≤ ENNReal.ofReal t then
    ed α (M.T 0 ω).toReal * ENNReal.ofReal (f (t - (M.T 0 ω).toReal)) else 0 with hG
  have hT0m : Measurable fun ω => (M.T 0 ω).toReal := (M.measurable_T 0).ennreal_toReal
  have hedm : Measurable fun ω => ed α (M.T 0 ω).toReal := (measurable_ed α).comp hT0m
  -- the delayed identity
  have hid : ∀ t : ℝ, 0 ≤ t → Real.exp (α * t) *
      (M.P {ω | M.T 0 ω ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < M.Γ ω}).toReal =
        (∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, G t ω ∂M.P).toReal := by
    intro t ht
    have h := hDS t ht
    simp only [Set.mem_univ, true_and] at h
    rw [P_strad_eq M hreg t] at h
    rw [h, ← ENNReal.toReal_ofReal (Real.exp_pos (α * t)).le, ← ENNReal.toReal_mul,
      ← lintegral_const_mul' (ENNReal.ofReal (Real.exp (α * t))) _ ENNReal.ofReal_ne_top]
    congr 1
    refine setLIntegral_congr_fun hS0m fun ω _ => ?_
    simp only [hG]
    split_ifs with hT
    · rw [P_strad_eq M' hreg' (t - (M.T 0 ω).toReal)]
      have hset : {ω' | M'.T 0 ω' ≤ ENNReal.ofReal (t - (M.T 0 ω).toReal) ∧
          ENNReal.ofReal (t - (M.T 0 ω).toReal) < M'.Γ ω'} =
          {ω' | ENNReal.ofReal (t - (M.T 0 ω).toReal) < M'.Γ ω'} := by
        ext ω'; simp [h0']
      rw [hset]
      simp only [hf, hφ]
      unfold ed
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (measure_ne_top _ _),
        ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3
      ring
    · simp
  -- dominated convergence
  have hDCT : Tendsto (fun t => ∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, G t ω ∂M.P) atTop
      (𝓝 (∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, ed α (M.T 0 ω).toReal * ENNReal.ofReal c1 ∂M.P)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun ω => ed α (M.T 0 ω).toReal * ENNReal.ofReal C)
      (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_) ?_ ?_
    · exact Measurable.ite (measurableSet_le (M.measurable_T 0) measurable_const)
        (hedm.mul (hfmeas.comp (measurable_const.sub hT0m)).ennreal_ofReal) measurable_const
    · refine Eventually.of_forall fun ω => ?_
      simp only [hG]
      split_ifs
      · gcongr; exact hC _
      · exact bot_le
    · rw [lintegral_mul_const _ hedm]
      exact ENNReal.mul_ne_top (hLdef ▸ hLtop).ne ENNReal.ofReal_ne_top
    · refine ae_restrict_of_forall_mem hS0m fun ω hω => ?_
      have hfin := T0_ne_top M hω
      have hev : ∀ᶠ t in atTop, ed α (M.T 0 ω).toReal * ENNReal.ofReal (f (t - (M.T 0 ω).toReal)) =
          G t ω := (eventually_ge_atTop (M.T 0 ω).toReal).mono fun t ht => by
        simp only [hG]
        rw [if_pos]
        calc M.T 0 ω = ENNReal.ofReal (M.T 0 ω).toReal := (ENNReal.ofReal_toReal hfin).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal ht
      refine Tendsto.congr' hev ?_
      refine ENNReal.Tendsto.const_mul ?_ (Or.inr (by unfold ed; exact ENNReal.ofReal_ne_top))
      have hsub : Tendsto (fun t : ℝ => t - (M.T 0 ω).toReal) atTop atTop :=
        tendsto_atTop_atTop.2 fun b => ⟨b + (M.T 0 ω).toReal, fun t ht => by linarith⟩
      exact (ENNReal.continuous_ofReal.tendsto c1).comp (hflim.comp hsub)
  have hlimG : Tendsto (fun t => (∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, G t ω ∂M.P).toReal) atTop
      (𝓝 (L.toReal * c1)) := by
    rw [lintegral_mul_const _ hedm, ← hLdef] at hDCT
    have := (ENNReal.tendsto_toReal (ENNReal.mul_ne_top hLtop.ne ENNReal.ofReal_ne_top)).comp hDCT
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc1.le] at this
  have hsplit : ∀ t : ℝ, M.P {ω | ENNReal.ofReal t < M.Γ ω} =
      M.P {ω | ENNReal.ofReal t < min (M.T 0 ω) (M.Γ ω)} +
        M.P {ω | M.T 0 ω ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < M.Γ ω} := by
    intro t
    have hdis : Disjoint {ω | ENNReal.ofReal t < min (M.T 0 ω) (M.Γ ω)}
        {ω | M.T 0 ω ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < M.Γ ω} :=
      Set.disjoint_left.2 fun ω ha hb => absurd hb.1 (not_le.2 (lt_min_iff.1 ha).1)
    have hm2 : MeasurableSet {ω | M.T 0 ω ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < M.Γ ω} :=
      (measurableSet_le (M.measurable_T 0) measurable_const).inter
        (measurableSet_lt measurable_const (measurable_Γ M))
    rw [← measure_union hdis hm2]
    congr 1
    ext ω
    simp only [Set.mem_union, Set.mem_setOf_eq, lt_min_iff]
    constructor
    · intro h
      by_cases hT : M.T 0 ω ≤ ENNReal.ofReal t
      · exact Or.inr ⟨hT, h⟩
      · exact Or.inl ⟨not_le.1 hT, h⟩
    · rintro (h | h)
      · exact h.2
      · exact h.2
  have hsum := h6.add (hlimG.congr' ((eventually_ge_atTop 0).mono fun t ht => (hid t ht).symm))
  rw [zero_add] at hsum
  rw [hc2]
  refine hsum.congr' ((eventually_ge_atTop 0).mono fun t _ => ?_)
  simp only
  rw [hsplit t, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

end TabooRegen.Prop3

open MeasureTheory Filter Topology TabooRegen TabooRegen.Model in
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (h2 : M.A2) (h3 : M.A3 α)
    (h4 : M.A4 α) (h5 : M.A5 α) (h6 : M.A6 α) :
    0 < M.c2 α ∧
      Tendsto (fun t : ℝ => Real.exp (α * t) * (M.P {ω | ENNReal.ofReal t < M.Γ ω}).toReal)
        atTop (𝓝 (M.c2 α)) := by
  have hP := TabooRegen.Prop3.P_S0_ne_zero M h1
  obtain ⟨M', hreg', h0', hA1, hA2, hA3, hA4, -, hrate, hcw, -, hds⟩ :=
    TabooRegen.delay_shift M hreg hP
  obtain ⟨hc1, hlim⟩ := TabooRegen.proposition_2 M' hreg' h0' ((hA1 α).2 h1) (hA2.2 h2)
    ((hA3 α).2 h3) ((hA4 α).2 h4)
  exact TabooRegen.Prop3.prop3_core M hreg h1 h5 h6 M' hreg' h0' hc1 hlim (hrate α) (hcw α)
    (fun t ht => hds 0 Set.univ MeasurableSet.univ t ht)
