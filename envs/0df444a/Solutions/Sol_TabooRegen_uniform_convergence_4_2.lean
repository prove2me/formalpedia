-- Prove2me | solution 1 for TabooRegen.uniform_convergence_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T18:03:37.179646+00:00
-- url     : https://prove2.me/submissions/c5857f1f-315a-4adf-8aee-dc069e2a63fc

import Mathlib
import Definitions.Def_TabooRegen_Window
import Theorems.Thm_TabooRegen_uniform_key_renewal
import Theorems.Thm_TabooRegen_renewal_decomposition_4_2
import Theorems.Thm_TabooRegen_chernoff_tail
import Theorems.Thm_TabooRegen_exp_moment_of_A7

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

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

end TabooRegen.Twist

section GlueSec
open QueueingFundamentals.MG1
namespace SmithRegenerative.Equilibrium.T2Glue

open SmithRegenerative.Equilibrium

/-! ## G0: local finiteness of the renewal measure (Chernoff bound; adapted from Sol_pv_b630d11e) -/

noncomputable def expMom (l : ℝ) (ρ : Measure ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-(l * x))) ∂ρ

lemma measurable_expden (l : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-(l * x)))) := by
  fun_prop

lemma expMom_conv (l : ℝ) (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ] :
    expMom l (ρ ∗ σ) = expMom l ρ * expMom l σ := by
  unfold expMom
  rw [Measure.lintegral_conv (measurable_expden l)]
  have : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-(l * (x + y)))) =
      ENNReal.ofReal (Real.exp (-(l * x))) * ENNReal.ofReal (Real.exp (-(l * y))) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
  simp only [this]
  simp only [lintegral_const_mul _ (measurable_expden l)]
  rw [lintegral_mul_const _ (measurable_expden l)]

lemma convPow_isProb (η : Measure ℝ) [IsProbabilityMeasure η] :
    ∀ n, IsProbabilityMeasure (convPow η n)
  | 0 => by rw [convPow]; infer_instance
  | n + 1 => by
      have := convPow_isProb η n
      rw [convPow]; infer_instance

lemma expMom_convPow (η : Measure ℝ) [IsProbabilityMeasure η] (l : ℝ) :
    ∀ n, expMom l (convPow η n) = expMom l η ^ n
  | 0 => by simp [convPow, expMom, lintegral_dirac]
  | n + 1 => by
    have := convPow_isProb η n
    simp only [convPow]
    rw [expMom_conv, expMom_convPow η l n, pow_succ]

lemma meas_Iic_le (l : ℝ) (hl : 0 < l) (ρ : Measure ℝ) (y : ℝ) :
    ρ (Set.Iic y) ≤ ENNReal.ofReal (Real.exp (l * y)) * expMom l ρ := by
  rw [expMom, ← lintegral_const_mul _ (measurable_expden l),
    ← lintegral_indicator_one measurableSet_Iic]
  refine lintegral_mono (fun x => ?_)
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs with hx
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ENNReal.one_le_ofReal,
      Real.one_le_exp_iff]
    have : x ≤ y := hx
    nlinarith
  · exact bot_le

lemma renewal_Iic_le (K F : Measure ℝ) [SFinite K] [IsProbabilityMeasure F]
    (l : ℝ) (hl : 0 < l) (y : ℝ) :
    renewalMeasure K F (Set.Iic y) ≤
      ENNReal.ofReal (Real.exp (l * y)) * expMom l K * (1 - expMom l F)⁻¹ := by
  rw [renewalMeasure, Measure.sum_apply _ measurableSet_Iic, ← ENNReal.tsum_geometric,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  have := convPow_isProb F n
  refine (meas_Iic_le l hl _ y).trans (le_of_eq ?_)
  rw [expMom_conv, expMom_convPow F l n, mul_assoc]

/-- A cycle law has positive mass on `(0, ∞)`. -/
lemma cycle_Ioi_pos (F : Measure ℝ) (hF : IsCycleLaw F) : 0 < F (Set.Ioi 0) := by
  obtain ⟨hP, hneg, hne⟩ := hF
  rw [pos_iff_ne_zero]
  intro h0
  apply hne
  ext s hs
  have hc : F {(0:ℝ)}ᶜ = 0 := by
    have : ({(0:ℝ)}ᶜ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      constructor
      · intro h; exact lt_or_gt_of_ne h
      · rintro (h|h)
        · exact h.ne
        · exact h.ne'
    rw [this]; exact measure_union_null hneg h0
  have h1 : F {(0:ℝ)} = 1 := by
    have := measure_add_measure_compl (μ := F) (measurableSet_singleton (0:ℝ))
    rw [hc, add_zero, measure_univ] at this; exact this
  by_cases h : (0:ℝ) ∈ s
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_mem h, Pi.one_apply]
    apply le_antisymm (prob_le_one)
    rw [← h1]; exact measure_mono (Set.singleton_subset_iff.mpr h)
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem h]
    exact measure_mono_null (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; rintro rfl; exact h hx) hc

lemma expMom_lt_one (F : Measure ℝ) (hF : IsCycleLaw F) (l : ℝ) (hl : 0 < l) :
    expMom l F < 1 := by
  have hP := hF.1
  have hneg := hF.2.1
  have hpos := cycle_Ioi_pos F hF
  -- some δ > 0 with F (Ioi δ) > 0
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ 0 < F (Set.Ioi δ) := by
    by_contra hcon
    push_neg at hcon
    have : Set.Ioi (0:ℝ) = ⋃ n : ℕ, Set.Ioi (1 / ((n:ℝ) + 1)) := by
      ext x; simp only [Set.mem_Ioi, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
        exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩; exact lt_trans (by positivity) hn
    have hnull : F (⋃ n : ℕ, Set.Ioi (1 / ((n:ℝ) + 1))) = 0 :=
      measure_iUnion_null (fun n => le_antisymm (hcon _ (by positivity)) bot_le)
    rw [this] at hpos
    exact hpos.ne' hnull
  -- split the integral
  have hae : ∀ᵐ x ∂F, 0 ≤ x := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hneg
  have hbound : ∀ᵐ x ∂F, ENNReal.ofReal (Real.exp (-(l * x))) ≤
      (Set.Ioi δ).indicator (fun _ => ENNReal.ofReal (Real.exp (-(l * δ)))) x +
        (Set.Ioi δ)ᶜ.indicator (fun _ => 1) x := by
    filter_upwards [hae] with x hx
    by_cases hxδ : x ∈ Set.Ioi δ
    · rw [Set.indicator_of_mem hxδ, Set.indicator_of_notMem (by simpa using hxδ), add_zero]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have : δ < x := hxδ
      nlinarith
    · rw [Set.indicator_of_notMem hxδ, Set.indicator_of_mem (by simpa using hxδ), zero_add]
      rw [ENNReal.ofReal_le_one]
      apply Real.exp_le_one_iff.mpr
      nlinarith
  calc expMom l F ≤ ∫⁻ x, ((Set.Ioi δ).indicator (fun _ => ENNReal.ofReal (Real.exp (-(l * δ)))) x +
        (Set.Ioi δ)ᶜ.indicator (fun _ => 1) x) ∂F := lintegral_mono_ae hbound
    _ = ENNReal.ofReal (Real.exp (-(l * δ))) * F (Set.Ioi δ) + F (Set.Ioi δ)ᶜ := by
        rw [lintegral_add_left (Measurable.indicator measurable_const measurableSet_Ioi),
          lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Ioi.compl]
        simp
    _ < F (Set.Ioi δ) + F (Set.Ioi δ)ᶜ := by
        apply ENNReal.add_lt_add_right (measure_ne_top _ _)
        have hlt : ENNReal.ofReal (Real.exp (-(l * δ))) < 1 := by
          rw [ENNReal.ofReal_lt_one]
          calc Real.exp (-(l * δ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
            _ = 1 := Real.exp_zero
        calc ENNReal.ofReal (Real.exp (-(l * δ))) * F (Set.Ioi δ)
            < 1 * F (Set.Ioi δ) := by
              rw [mul_comm, mul_comm 1]
              exact ENNReal.mul_lt_mul_right hδF.ne' (measure_ne_top _ _) hlt
          _ = F (Set.Ioi δ) := one_mul _
    _ = 1 := by rw [measure_add_measure_compl measurableSet_Ioi, measure_univ]

lemma expMom_le_mass (K : Measure ℝ) (hK0 : K (Set.Iio 0) = 0) (l : ℝ) (hl : 0 ≤ l) :
    expMom l K ≤ K Set.univ := by
  have hae : ∀ᵐ x ∂K, 0 ≤ x := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hK0
  calc expMom l K ≤ ∫⁻ _, 1 ∂K := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with x hx
        rw [ENNReal.ofReal_le_one]; apply Real.exp_le_one_iff.mpr; nlinarith
    _ = K Set.univ := by simp

lemma renewal_Icc_lt_top (K F : Measure ℝ) [IsFiniteMeasure K] (hK0 : K (Set.Iio 0) = 0)
    (hF : IsCycleLaw F) (t : ℝ) :
    renewalMeasure K F (Set.Icc 0 t) < ⊤ := by
  have := hF.1
  refine lt_of_le_of_lt (measure_mono Set.Icc_subset_Iic_self) ?_
  refine lt_of_le_of_lt (renewal_Iic_le K F 1 one_pos t) ?_
  have h1 := expMom_lt_one F hF 1 one_pos
  have hK : expMom 1 K < ⊤ :=
    lt_of_le_of_lt (expMom_le_mass K hK0 1 zero_le_one) (measure_lt_top _ _)
  have h2 : (1 - expMom 1 F)⁻¹ ≠ ⊤ := by
    rw [Ne, ENNReal.inv_eq_top]; exact (tsub_pos_of_lt h1).ne'
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK) (lt_top_iff_ne_top.mpr h2)

end SmithRegenerative.Equilibrium.T2Glue
end GlueSec

namespace TabooRegen.Prop2

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen TabooRegen.Twist
open SmithRegenerative.Equilibrium

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

lemma τ1_eq (h0 : ∀ ω, M.T 0 ω = 0) (ω : Ω) : M.τ 1 ω = M.T 1 ω := by
  simp [Model.τ, Model.Tm, prevTime, h0]

lemma T1_pos (h0 : ∀ ω, M.T 0 ω = 0) (ω : Ω) : 0 < M.T 1 ω := by
  have h := M.T_strict 0 ω (by rw [h0]; exact ENNReal.zero_lt_top)
  rwa [h0] at h

lemma T1_ne_top (h0 : ∀ ω, M.T 0 ω = 0) {ω : Ω} (hω : ω ∈ M.NoExit 1) : M.T 1 ω ≠ ⊤ := by
  have hle : M.T 0 ω ≤ M.Γ ω := by rw [h0]; exact bot_le
  have h1 : M.T (0 + 1) ω ≤ M.Γ ω := le_Γ_succ M hle hω
  intro htop
  have hΓ := M.T_top 1 ω htop
  rw [zero_add, htop] at h1
  exact absurd (top_le_iff.1 h1) hΓ.ne

lemma τ1_toReal_pos (h0 : ∀ ω, M.T 0 ω = 0) {ω : Ω} (hω : ω ∈ M.NoExit 1) :
    0 < (M.τ 1 ω).toReal := by
  rw [τ1_eq M h0]
  exact ENNReal.toReal_pos (T1_pos M h0 ω).ne' (T1_ne_top M h0 hω)

lemma Gtilde_univ {α : ℝ} (h1 : M.A1 α) : M.Gtilde α Set.univ = 1 := by
  rw [← lintegral_one, lintegral_Gtilde M α measurable_const]
  simp only [mul_one]
  exact h1.2

lemma Gtilde_Iio (α : ℝ) : M.Gtilde α (Set.Iio 0) = 0 := by
  rw [← lintegral_indicator_one measurableSet_Iio,
    lintegral_Gtilde M α (measurable_one.indicator measurableSet_Iio)]
  have h : ∀ ω, (Set.Iio (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞) (M.τ 1 ω).toReal = 0 :=
    fun ω => Set.indicator_of_notMem (s := Set.Iio (0 : ℝ))
      (by simp only [Set.mem_Iio, not_lt]; exact ENNReal.toReal_nonneg) _
  simp [h]

lemma mean_Gtilde (α : ℝ) : mean (M.Gtilde α) = M.lamInv α := by
  unfold mean Model.lamInv
  rw [lintegral_Gtilde M α ENNReal.measurable_ofReal]
  exact lintegral_congr fun ω => mul_comm _ _

lemma Q_noExit_pos {α : ℝ} (h1 : M.A1 α) : 0 < M.Q (M.NoExit 1) := by
  refine pos_iff_ne_zero.2 fun h => ?_
  have h2 := h1.2
  unfold Model.cycleMGF at h2
  rw [Measure.restrict_eq_zero.2 h, lintegral_zero_measure] at h2
  exact zero_ne_one h2

lemma pos_tau (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α) :
    0 < ∫⁻ ω in M.NoExit 1, ENNReal.ofReal (M.τ 1 ω).toReal ∂M.Q := by
  have hm : Measurable fun ω => ENNReal.ofReal (M.τ 1 ω).toReal :=
    ENNReal.measurable_ofReal.comp (measurable_τ' M 1).ennreal_toReal
  rw [lintegral_pos_iff_support hm, Measure.restrict_apply' (measurableSet_NoExit M 1)]
  have hsub : Function.support (fun ω => ENNReal.ofReal (M.τ 1 ω).toReal) ∩ M.NoExit 1 =
      M.NoExit 1 := by
    refine Set.inter_eq_right.2 fun ω hω => ?_
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact τ1_toReal_pos M h0 hω
  rw [hsub]
  exact Q_noExit_pos M h1

lemma ed_ge_one {α : ℝ} (hα : 0 ≤ α) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ ENNReal.ofReal (Real.exp (α * x)) := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hα hx))

lemma lamInv_pos (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α) : 0 < M.lamInv α := by
  refine lt_of_lt_of_le (pos_tau M h0 h1) ?_
  unfold Model.lamInv
  refine lintegral_mono fun ω => ?_
  calc ENNReal.ofReal (M.τ 1 ω).toReal = ENNReal.ofReal (M.τ 1 ω).toReal * 1 := (mul_one _).symm
    _ ≤ _ := by gcongr; exact ed_ge_one h1.1 ENNReal.toReal_nonneg

lemma cycleWeight_pos (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α) : 0 < M.cycleWeight α := by
  refine lt_of_lt_of_le (pos_tau M h0 h1) ?_
  unfold Model.cycleWeight
  rw [← lintegral_indicator (measurableSet_NoExit M 1)]
  refine lintegral_mono fun ω => ?_
  by_cases hω : ω ∈ M.NoExit 1
  · rw [Set.indicator_of_mem hω]
    have hτ := τ1_toReal_pos M h0 hω
    have hτf : M.τ 1 ω ≠ ⊤ := by rw [τ1_eq M h0]; exact T1_ne_top M h0 hω
    have hsub : Set.Ico 0 (M.τ 1 ω).toReal ⊆
        {u : ℝ | 0 ≤ u ∧ ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)} := by
      intro u hu
      refine ⟨hu.1, ?_⟩
      have hγ : M.γ 1 ω = ⊤ := hω
      rw [hγ, min_eq_right le_top]
      exact (ENNReal.ofReal_lt_iff_lt_toReal hu.1 hτf).2 hu.2
    calc ENNReal.ofReal (M.τ 1 ω).toReal = ∫⁻ u in Set.Ico 0 (M.τ 1 ω).toReal, 1 := by
          rw [setLIntegral_one, Real.volume_Ico, sub_zero]
      _ ≤ ∫⁻ u in Set.Ico 0 (M.τ 1 ω).toReal, ENNReal.ofReal (Real.exp (α * u)) :=
          setLIntegral_mono (ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
            fun u hu => ed_ge_one h1.1 hu.1
      _ ≤ _ := lintegral_mono_set hsub
  · rw [Set.indicator_of_notMem hω]; exact bot_le

lemma isCycleLaw_Gtilde (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α) :
    IsCycleLaw (M.Gtilde α) := by
  refine ⟨⟨Gtilde_univ M h1⟩, Gtilde_Iio M α, fun h => ?_⟩
  have hm := mean_Gtilde M α
  rw [h] at hm
  unfold mean at hm
  rw [lintegral_dirac, ENNReal.ofReal_zero] at hm
  exact (lamInv_pos M h0 h1).ne hm

lemma isDelayLaw_dirac : IsDelayLaw (Measure.dirac (0 : ℝ)) := by
  refine ⟨?_, by simp⟩
  rw [Measure.dirac_apply' _ measurableSet_Iio]
  simp

lemma sfinite_convPow' (F : Measure ℝ) [SFinite F] (n : ℕ) :
    SFinite (QueueingFundamentals.MG1.convPow F n) := by
  induction n with
  | zero => simp only [QueueingFundamentals.MG1.convPow]; infer_instance
  | succ n ih =>
    simp only [QueueingFundamentals.MG1.convPow]
    unfold Measure.conv
    infer_instance

lemma ac_convPow (F F' : Measure ℝ) [SFinite F] [SFinite F'] (h : F ≪ F') (n : ℕ) :
    QueueingFundamentals.MG1.convPow F n ≪ QueueingFundamentals.MG1.convPow F' n := by
  induction n with
  | zero => exact Measure.AbsolutelyContinuous.rfl
  | succ n ih =>
    have := sfinite_convPow' F n
    have := sfinite_convPow' F' n
    simp only [QueueingFundamentals.MG1.convPow]
    unfold Measure.conv
    exact (ih.prod h).map measurable_add

lemma inClassS_Gtilde {α : ℝ} (h2 : M.A2) : InClassS (M.Gtilde α) := by
  have := Q_finite' M
  have hG : SFinite M.G := by unfold Model.G; infer_instance
  have hGt := sfinite_Gtilde M α
  have hac : M.G ≪ M.Gtilde α := by
    unfold Model.Gtilde
    refine withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul measurable_id))).aemeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.exp_pos]
  obtain ⟨k, hk, hns⟩ := h2
  exact ⟨k, hk, fun hms => hns (hms.mono_ac (ac_convPow M.G (M.Gtilde α) hac k)
    Measure.AbsolutelyContinuous.rfl)⟩

end TabooRegen.Prop2


/-! ## ad51b63d glue, part 1: pathwise representation of `b̃` (no factorization over past cycles) -/
namespace TabooRegen.UC

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- the event of `b̃_{B,ℓ}` written at lag `r = s - T(ℓ)` after `T(ℓ)` -/
def Ev (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ) (ω : Ω) : Prop :=
  M.T ℓ ω ≠ ⊤ ∧ 0 ≤ r ∧ ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), r) ∈ B ∧
    ENNReal.ofReal ((M.T ℓ ω).toReal + r) < M.T (ℓ + 1) ω ∧
    ENNReal.ofReal ((M.T ℓ ω).toReal + r) < M.Γ ω

/-- the integrand: `e^{α(T(ℓ)+r)} 1{event at lag r}` -/
noncomputable def G (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  {p : ℝ × Ω | Ev M ℓ B p.1 p.2}.indicator
    (fun p => ENNReal.ofReal (Real.exp (α * ((M.T ℓ p.2).toReal + p.1)))) (r, ω)

lemma measurableSet_Ev (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (hB : MeasurableSet B) :
    MeasurableSet {p : ℝ × Ω | Ev M ℓ B p.1 p.2} := by
  have hT : Measurable fun p : ℝ × Ω => M.T ℓ p.2 := (M.measurable_T ℓ).comp measurable_snd
  have hs : Measurable fun p : ℝ × Ω => ENNReal.ofReal ((M.T ℓ p.2).toReal + p.1) :=
    (hT.ennreal_toReal.add measurable_fst).ennreal_ofReal
  have hw : Measurable fun p : ℝ × Ω =>
      ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) p.2), p.1) :=
    (measurable_pi_lambda _ fun i => (M.measurable_W _).comp measurable_snd).prodMk measurable_fst
  refine (hT (measurableSet_singleton ⊤).compl).inter
    ((measurableSet_le measurable_const measurable_fst).inter ((hB.preimage hw).inter
      ((measurableSet_lt hs ((M.measurable_T (ℓ + 1)).comp measurable_snd)).inter
        (measurableSet_lt hs ((measurable_Γ M).comp measurable_snd)))))

lemma measurable_G (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) : Measurable fun p : ℝ × Ω => G M α ℓ B p.1 p.2 := by
  unfold G
  refine Measurable.indicator ?_ (measurableSet_Ev M ℓ B hB)
  exact (Real.measurable_exp.comp (measurable_const.mul
    (((M.measurable_T ℓ).comp measurable_snd).ennreal_toReal.add measurable_fst))).ennreal_ofReal

/-- pathwise: at `r = s - T(ℓ)` the integrand is `e^{αs}` times the indicator of the `b̃` event -/
lemma G_at (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (s : ℝ) (hs : 0 ≤ s)
    (ω : Ω) :
    G M α ℓ B (s - (M.T ℓ ω).toReal) ω =
      {ω | ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), s - (M.T ℓ ω).toReal) ∈ B ∧
        M.T ℓ ω ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < M.T (ℓ + 1) ω ∧
        ENNReal.ofReal s < M.Γ ω}.indicator (fun _ => ENNReal.ofReal (Real.exp (α * s))) ω := by
  have hadd : (M.T ℓ ω).toReal + (s - (M.T ℓ ω).toReal) = s := by ring
  have hiff' : M.T ℓ ω ≠ ⊤ → (M.T ℓ ω ≤ ENNReal.ofReal s ↔ 0 ≤ s - (M.T ℓ ω).toReal) := by
    intro hT
    rw [sub_nonneg, ← ENNReal.ofReal_toReal hT, ENNReal.ofReal_le_ofReal_iff hs,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  have hiff : Ev M ℓ B (s - (M.T ℓ ω).toReal) ω ↔
      (((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), s - (M.T ℓ ω).toReal) ∈ B ∧
        M.T ℓ ω ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < M.T (ℓ + 1) ω ∧
        ENNReal.ofReal s < M.Γ ω) := by
    unfold Ev
    rw [hadd]
    constructor
    · rintro ⟨hT, hc, hB, h1, h2⟩
      exact ⟨hB, (hiff' hT).2 hc, h1, h2⟩
    · rintro ⟨hB, hle, h1, h2⟩
      have hT : M.T ℓ ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
      exact ⟨hT, (hiff' hT).1 hle, hB, h1, h2⟩
  unfold G
  by_cases h : Ev M ℓ B (s - (M.T ℓ ω).toReal) ω
  · rw [Set.indicator_of_mem (show ((s - (M.T ℓ ω).toReal, ω) : ℝ × Ω) ∈
        {p : ℝ × Ω | Ev M ℓ B p.1 p.2} from h),
      Set.indicator_of_mem (show ω ∈ {ω | ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω),
        s - (M.T ℓ ω).toReal) ∈ B ∧ M.T ℓ ω ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < M.T (ℓ + 1) ω ∧
        ENNReal.ofReal s < M.Γ ω} from hiff.1 h)]
    simp only [hadd]
  · rw [Set.indicator_of_notMem (show ((s - (M.T ℓ ω).toReal, ω) : ℝ × Ω) ∉
        {p : ℝ × Ω | Ev M ℓ B p.1 p.2} from h),
      Set.indicator_of_notMem (show ω ∉ {ω | ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω),
        s - (M.T ℓ ω).toReal) ∈ B ∧ M.T ℓ ω ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < M.T (ℓ + 1) ω ∧
        ENNReal.ofReal s < M.Γ ω} from fun h' => h (hiff.2 h'))]

/-- **pathwise representation**: `b̃_{B,ℓ}(s) = E[G(s - T(ℓ))]` for `s ⩾ 0` -/
theorem btilde_rep (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) (s : ℝ) (hs : 0 ≤ s) :
    ENNReal.ofReal (M.btilde α ℓ B s) = ∫⁻ ω, G M α ℓ B (s - (M.T ℓ ω).toReal) ω ∂M.P := by
  have : IsProbabilityMeasure M.P := M.isProb
  have hE : MeasurableSet {ω | ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), s - (M.T ℓ ω).toReal) ∈ B ∧
        M.T ℓ ω ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < M.T (ℓ + 1) ω ∧
        ENNReal.ofReal s < M.Γ ω} := by
    have hw : Measurable fun ω : Ω =>
        ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), s - (M.T ℓ ω).toReal) :=
      (measurable_pi_lambda _ fun i => M.measurable_W _).prodMk
        (measurable_const.sub (M.measurable_T ℓ).ennreal_toReal)
    exact (hB.preimage hw).inter ((measurableSet_le (M.measurable_T ℓ) measurable_const).inter
      ((measurableSet_lt measurable_const (M.measurable_T (ℓ + 1))).inter
        (measurableSet_lt measurable_const (measurable_Γ M))))
  simp_rw [G_at M α ℓ B s hs]
  rw [lintegral_indicator_const hE, Model.btilde, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- the future-cycle factor at lag `r`: `e^{αr} 1{0 ≤ r, r < γ ∧ τ of the first future cycle}` -/
noncomputable def Hr (α r : ℝ) (x : ℕ → Path S) : ℝ≥0∞ :=
  {x : ℕ → Path S | 0 ≤ r ∧ ENNReal.ofReal r < min (exitTime A (x 0).1) (len (x 0))}.indicator
    (fun _ => ENNReal.ofReal (Real.exp (α * r))) x

lemma measurable_Hr (hγ : Measurable fun x : Path S => exitTime A x.1) (α r : ℝ) :
    Measurable (Hr (A := A) (S := S) α r) := by
  unfold Hr
  refine measurable_const.indicator ?_
  have h0 : Measurable fun x : ℕ → Path S => x 0 := measurable_pi_apply 0
  exact (MeasurableSet.const (0 ≤ r)).inter
    (measurableSet_lt measurable_const ((hγ.comp h0).min (measurable_len.comp h0)))

/-- pathwise domination of the integrand by a product of a `T(ℓ)`-factor and a future-cycle factor -/
lemma G_le (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ) (ω : Ω) :
    G M α ℓ B r ω ≤ {ω | M.T ℓ ω ≤ M.Γ ω}.indicator
      (fun ω => ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal))) ω *
        Hr (A := A) α r (cycj M ℓ ω) := by
  unfold G
  by_cases h : Ev M ℓ B r ω
  · obtain ⟨hT, hr, hB, h1, h2⟩ := h
    have hTe : (M.T ℓ ω) = ENNReal.ofReal (M.T ℓ ω).toReal := (ENNReal.ofReal_toReal hT).symm
    have hsum : ENNReal.ofReal ((M.T ℓ ω).toReal + r) = M.T ℓ ω + ENNReal.ofReal r := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hr, ← hTe]
    rw [hsum] at h1 h2
    have hΓ : M.T ℓ ω ≤ M.Γ ω := (le_self_add).trans h2.le
    have hτ : ENNReal.ofReal r < len (cycj M ℓ ω 0) := by
      have hc : cycj M ℓ ω 0 = M.W (ℓ + 1) ω := by simp [cycj]
      rw [hc, len_W]
      show ENNReal.ofReal r < M.T (ℓ + 1) ω - M.Tm (ℓ + 1) ω
      have hTm : M.Tm (ℓ + 1) ω = M.T ℓ ω := by simp [Model.Tm, prevTime]
      rw [hTm]
      exact lt_of_not_ge fun hle => absurd h1 (not_lt.2 (tsub_le_iff_left.1 hle))
    have hγ : ENNReal.ofReal r < exitTime A (cycj M ℓ ω 0).1 := by
      have hc : exitTime A (cycj M ℓ ω 0).1 = M.γ (ℓ + 1) ω := by simp [cycj, Model.γ]
      rw [hc]
      have h3 := h2.trans_le (Γ_le_Tm_add_γ M ω (ℓ + 1))
      have hTm : M.Tm (ℓ + 1) ω = M.T ℓ ω := by simp [Model.Tm, prevTime]
      rw [hTm] at h3
      exact (ENNReal.add_lt_add_iff_left hT).1 h3
    rw [Set.indicator_of_mem (show ((r, ω) : ℝ × Ω) ∈ {p : ℝ × Ω | Ev M ℓ B p.1 p.2} from
        ⟨hT, hr, hB, by rw [hsum]; exact h1, by rw [hsum]; exact h2⟩),
      Set.indicator_of_mem (show ω ∈ {ω | M.T ℓ ω ≤ M.Γ ω} from hΓ), Hr,
      Set.indicator_of_mem (show cycj M ℓ ω ∈ {x : ℕ → Path S | 0 ≤ r ∧
        ENNReal.ofReal r < min (exitTime A (x 0).1) (len (x 0))} from ⟨hr, lt_min hγ hτ⟩),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]
  · rw [Set.indicator_of_notMem (show ((r, ω) : ℝ × Ω) ∉ {p : ℝ × Ω | Ev M ℓ B p.1 p.2} from h)]
    positivity

/-- **domination after integrating**: by Definition 2 at `n = ℓ` the bound factorizes -/
theorem lintegral_G_le (hreg : M.IsWideSenseTabooRegen) (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ)
    (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ) (φ : ℝ≥0∞ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ ω, φ (M.T ℓ ω) * G M α ℓ B r ω ∂M.P ≤
      (∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, φ (M.T ℓ ω) *
        ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) ∂M.P) *
        ∫⁻ x, Hr (A := A) α r x ∂(M.Q.map (cyc M)) := by
  have := M.isProb
  have := Q_finite' M
  have hE := measurableSet_le_Γ M ℓ
  have hg : Measurable fun ω => (M.T ℓ ω, cycj M ℓ ω) :=
    (M.measurable_T ℓ).prodMk (measurable_cycj M ℓ)
  have hf1 : Measurable fun v : ℝ≥0∞ => φ v * ENNReal.ofReal (Real.exp (α * v.toReal)) :=
    hφ.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id.ennreal_toReal)).ennreal_ofReal
  calc ∫⁻ ω, φ (M.T ℓ ω) * G M α ℓ B r ω ∂M.P
      ≤ ∫⁻ ω, {ω | M.T ℓ ω ≤ M.Γ ω}.indicator (fun ω =>
          (φ (M.T ℓ ω) * ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal))) *
            Hr (A := A) α r (cycj M ℓ ω)) ω ∂M.P := by
        refine lintegral_mono fun ω => ?_
        refine (mul_le_mul' le_rfl (G_le M α hα ℓ B r ω)).trans (le_of_eq ?_)
        by_cases hω : ω ∈ {ω | M.T ℓ ω ≤ M.Γ ω}
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, mul_assoc]
        · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul, mul_zero]
    _ = ∫⁻ p, (φ p.1 * ENNReal.ofReal (Real.exp (α * p.1.toReal))) * Hr (A := A) α r p.2
          ∂((M.P.restrict {ω | M.T ℓ ω ≤ M.Γ ω}).map fun ω => (M.T ℓ ω, cycj M ℓ ω)) := by
        have hmeas : Measurable fun p : ℝ≥0∞ × (ℕ → Path S) =>
            (φ p.1 * ENNReal.ofReal (Real.exp (α * p.1.toReal))) * Hr (A := A) α r p.2 :=
          (hf1.comp measurable_fst).mul ((measurable_Hr M.exit_measurable α r).comp measurable_snd)
        rw [lintegral_indicator hE]
        exact (lintegral_map hmeas hg).symm
    _ = _ := by
        rw [prod_law_j M hreg ℓ, lintegral_prod_mul hf1.aemeasurable
          (measurable_Hr M.exit_measurable α r).aemeasurable, lintegral_map hf1 (M.measurable_T ℓ)]

/-- the future-cycle factor integrates to `e^{αr} Q(r < γ₁ ∧ τ₁)` -/
lemma lintegral_Hr (α r : ℝ) (hr : 0 ≤ r) :
    ∫⁻ x, Hr (A := A) α r x ∂(M.Q.map (cyc M)) =
      ENNReal.ofReal (Real.exp (α * r)) * M.Q {ω | ENNReal.ofReal r < min (M.γ 1 ω) (M.τ 1 ω)} := by
  have hm := measurable_Hr M.exit_measurable α r
  rw [lintegral_map hm (measurable_cyc' M)]
  have hpt : ∀ ω, Hr (A := A) α r (cyc M ω) = {ω | ENNReal.ofReal r < min (M.γ 1 ω) (M.τ 1 ω)}.indicator
      (fun _ => ENNReal.ofReal (Real.exp (α * r))) ω := by
    intro ω
    have hc : cyc M ω 0 = M.W 1 ω := by simp [cyc]
    have hlen : len (cyc M ω 0) = M.τ 1 ω := by rw [hc, len_W]
    have hex : exitTime A (cyc M ω 0).1 = M.γ 1 ω := by rw [hc]; rfl
    unfold Hr
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hlen, hex, hr, true_and]
  simp_rw [hpt]
  have hτ : Measurable (M.τ 1) := by
    have e : M.τ 1 = fun ω => M.T 1 ω - M.T 0 ω := by
      funext ω; simp [Model.τ, Model.Tm, prevTime]
    rw [e]
    exact (M.measurable_T 1).sub (M.measurable_T 0)
  have hγ : Measurable (M.γ 1) := M.exit_measurable.comp (M.measurable_W 1)
  rw [lintegral_indicator_const (measurableSet_lt measurable_const (hγ.min hτ))]

end TabooRegen.UC

/-! ## ad51b63d glue, part 2 (L4): Tonelli representations -/
namespace TabooRegen.UC

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- the convolution `∫_{[0,t]} b̃(t-u) dU(u)` as an iterated lintegral over `ω` -/
theorem conv_rep (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) (U : Measure ℝ) [SFinite U] (t : ℝ) :
    ∫⁻ u in Set.Icc 0 t, ENNReal.ofReal (M.btilde α ℓ B (t - u)) ∂U =
      ∫⁻ ω, ∫⁻ u in Set.Icc 0 t, G M α ℓ B (t - u - (M.T ℓ ω).toReal) ω ∂U ∂M.P := by
  have := M.isProb
  have h1 : ∫⁻ u in Set.Icc 0 t, ENNReal.ofReal (M.btilde α ℓ B (t - u)) ∂U =
      ∫⁻ u in Set.Icc 0 t, ∫⁻ ω, G M α ℓ B (t - u - (M.T ℓ ω).toReal) ω ∂M.P ∂U := by
    refine setLIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    exact btilde_rep M α ℓ B hB (t - u) (by linarith [hu.2])
  rw [h1]
  have hm : Measurable fun p : ℝ × Ω => G M α ℓ B (t - p.1 - (M.T ℓ p.2).toReal) p.2 :=
    (measurable_G M α ℓ B hB).comp
      (((measurable_const.sub measurable_fst).sub
        ((M.measurable_T ℓ).comp measurable_snd).ennreal_toReal).prodMk measurable_snd)
  exact lintegral_lintegral_swap hm.aemeasurable

/-- the integral `∫_{(0,∞)} b̃` as an iterated lintegral over `ω` -/
theorem int_rep (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) :
    ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (M.btilde α ℓ B s) =
      ∫⁻ ω, (∫⁻ s in Set.Ioi 0, G M α ℓ B (s - (M.T ℓ ω).toReal) ω) ∂M.P := by
  have := M.isProb
  have h1 : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (M.btilde α ℓ B s) =
      ∫⁻ s in Set.Ioi 0, ∫⁻ ω, G M α ℓ B (s - (M.T ℓ ω).toReal) ω ∂M.P := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    exact btilde_rep M α ℓ B hB s (le_of_lt hs)
  rw [h1]
  have hm : Measurable fun p : ℝ × Ω => G M α ℓ B (p.1 - (M.T ℓ p.2).toReal) p.2 :=
    (measurable_G M α ℓ B hB).comp
      ((measurable_fst.sub ((M.measurable_T ℓ).comp measurable_snd).ennreal_toReal).prodMk
        measurable_snd)
  exact lintegral_lintegral_swap hm.aemeasurable

end TabooRegen.UC

/-! ## ad51b63d glue, part 3 (L6a): abstract renewal estimates and the factorization bound -/
namespace TabooRegen.UC

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen TabooRegen.Twist

/-- the uniform key renewal property, transferred to non-negative extended integrands -/
lemma ukr_lin (U : Measure ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (h : ℝ → ℝ)
    (hpos : ∀ r, 0 ≤ r → 0 ≤ h r) (hh : AntitoneOn h (Set.Ici 0))
    (hhi : IntegrableOn h (Set.Ici 0)) (hU : ∀ x, U (Set.Icc 0 x) < ⊤) (ε s : ℝ)
    (hukr : ∀ b : ℝ → ℝ, Measurable b → (∀ r, 0 ≤ r → |b r| ≤ h r) →
      |∫ u in Set.Icc 0 s, b (s - u) ∂U - lam * ∫ r in Set.Ioi 0, b r| ≤ ε)
    (b : ℝ → ℝ≥0∞) (hb : Measurable b) (hbh : ∀ r, 0 ≤ r → b r ≤ ENNReal.ofReal (h r)) :
    (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) ≤
        ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) + ENNReal.ofReal ε ∧
      ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) ≤
        (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) + ENNReal.ofReal ε := by
  have hb' : Measurable fun r => (b r).toReal := hb.ennreal_toReal
  have hbd : ∀ r, 0 ≤ r → |(b r).toReal| ≤ h r := by
    intro r hr
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal (hpos r hr) (hbh r hr)
  have hR := hukr _ hb' hbd
  have hε : 0 ≤ ε := (abs_nonneg _).trans hR
  -- finiteness of both lintegrals
  have hI1 : ∫⁻ u in Set.Icc 0 s, b (s - u) ∂U < ⊤ := by
    calc ∫⁻ u in Set.Icc 0 s, b (s - u) ∂U ≤ ∫⁻ _ in Set.Icc 0 s, ENNReal.ofReal (h 0) ∂U := by
          refine setLIntegral_mono measurable_const fun u hu => ?_
          have hsu : 0 ≤ s - u := by linarith [hu.2]
          exact (hbh _ hsu).trans (ENNReal.ofReal_le_ofReal
            (hh (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hsu) hsu))
      _ = ENNReal.ofReal (h 0) * U (Set.Icc 0 s) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hU s)
  have hI2 : ∫⁻ r in Set.Ioi 0, b r < ⊤ := by
    calc ∫⁻ r in Set.Ioi 0, b r ≤ ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (h r) :=
          setLIntegral_mono' measurableSet_Ioi fun r hr => hbh r (le_of_lt hr)
      _ < ⊤ := (hhi.mono_set Set.Ioi_subset_Ici_self).lintegral_lt_top
  have hm1 : AEMeasurable (fun u => b (s - u)) (U.restrict (Set.Icc 0 s)) :=
    (hb.comp (measurable_const.sub measurable_id)).aemeasurable
  have e1 : ∫ u in Set.Icc 0 s, (b (s - u)).toReal ∂U =
      (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U).toReal := by
    refine integral_toReal hm1 ?_
    exact ae_lt_top' hm1 hI1.ne
  have e2 : ∫ r in Set.Ioi 0, (b r).toReal = (∫⁻ r in Set.Ioi 0, b r).toReal :=
    integral_toReal hb.aemeasurable (ae_lt_top' hb.aemeasurable hI2.ne)
  rw [e1, e2] at hR
  obtain ⟨I1, hI1d⟩ : ∃ I, ∫⁻ u in Set.Icc 0 s, b (s - u) ∂U = I := ⟨_, rfl⟩
  obtain ⟨I2, hI2d⟩ : ∃ I, ∫⁻ r in Set.Ioi 0, b r = I := ⟨_, rfl⟩
  rw [hI1d] at hI1 hR ⊢
  rw [hI2d] at hI2 hR ⊢
  have h1 := (abs_le.1 hR).1
  have h2 := (abs_le.1 hR).2
  have hn1 := ENNReal.toReal_nonneg (a := I1)
  have hn2 := ENNReal.toReal_nonneg (a := I2)
  constructor
  ·     calc I1 = ENNReal.ofReal I1.toReal := (ENNReal.ofReal_toReal hI1.ne).symm
      _ ≤ ENNReal.ofReal (lam * I2.toReal + ε) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal lam * I2 + ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_add (mul_nonneg hlam hn2) hε, ENNReal.ofReal_mul hlam,
            ENNReal.ofReal_toReal hI2.ne]
  · calc ENNReal.ofReal lam * I2 = ENNReal.ofReal (lam * I2.toReal) := by
          rw [ENNReal.ofReal_mul hlam, ENNReal.ofReal_toReal hI2.ne]
      _ ≤ ENNReal.ofReal (I1.toReal + ε) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = I1 + ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_add hn1 hε, ENNReal.ofReal_toReal hI1.ne]

/-- the convolution of a function vanishing on `(-∞, 0)` only sees `[0, s]` -/
lemma conv_shift (U : Measure ℝ) (b : ℝ → ℝ≥0∞) (hb0 : ∀ r, r < 0 → b r = 0) (s t : ℝ)
    (hst : s ≤ t) :
    ∫⁻ u in Set.Icc 0 t, b (s - u) ∂U = ∫⁻ u in Set.Icc 0 s, b (s - u) ∂U := by
  rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun u => ?_
  by_cases h1 : u ∈ Set.Icc 0 s
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show u ∈ Set.Icc 0 t from ⟨h1.1, h1.2.trans hst⟩)]
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : u ∈ Set.Icc 0 t
    · rw [Set.indicator_of_mem h2]
      apply hb0
      have : s < u := by
        by_contra hc
        exact h1 ⟨h2.1, not_lt.1 hc⟩
      linarith
    · rw [Set.indicator_of_notMem h2]

/-- translation invariance on `(0, ∞)` for a function vanishing on `(-∞, 0)` -/
lemma shift_Ioi (b : ℝ → ℝ≥0∞) (hb0 : ∀ r, r < 0 → b r = 0) (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ s in Set.Ioi 0, b (s - c) = ∫⁻ r in Set.Ioi 0, b r := by
  have hsupp1 : Function.support (fun s => b (s - c)) ⊆ Set.Ici 0 := by
    intro x hx
    by_contra hneg
    exact hx (hb0 _ (by simp only [Set.mem_Ici, not_le] at hneg; linarith))
  have hsupp2 : Function.support b ⊆ Set.Ici 0 := by
    intro x hx
    by_contra hneg
    exact hx (hb0 _ (by simpa using hneg))
  rw [setLIntegral_congr Ioi_ae_eq_Ici, setLIntegral_congr Ioi_ae_eq_Ici,
    setLIntegral_eq_of_support_subset hsupp1, setLIntegral_eq_of_support_subset hsupp2,
    lintegral_sub_right_eq_self]

/-- the tail of an integrable function on `[0, ∞)` is eventually small -/
lemma tail_small (h : ℝ → ℝ) (hhi : IntegrableOn h (Set.Ici 0)) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ N : ℕ, ∫⁻ r in Set.Ici (N : ℝ), ENNReal.ofReal (h r) < η := by
  set μ := (volume : Measure ℝ).restrict (Set.Ici 0)
  have hm : AEMeasurable (fun r => ENNReal.ofReal (h r)) μ := hhi.aemeasurable.ennreal_ofReal
  have hT : Tendsto (fun n : ℕ => ∫⁻ r, (Set.Ici (n : ℝ)).indicator
      (fun r => ENNReal.ofReal (h r)) r ∂μ) atTop (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun r => ENNReal.ofReal (h r))
      (fun n => hm.indicator measurableSet_Ici) (fun n => ?_) ?_ ?_
    · exact Filter.Eventually.of_forall fun r => Set.indicator_le_self _ _ r
    · exact hhi.lintegral_lt_top.ne
    · refine Filter.Eventually.of_forall fun r => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop ⌈r⌉₊] with n hn
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_Ici, not_le]
      exact lt_of_le_of_lt (Nat.le_ceil r) (by exact_mod_cast hn)
  rw [lintegral_zero] at hT
  obtain ⟨N, hN⟩ := (hT.eventually (gt_mem_nhds hη)).exists
  refine ⟨N, lt_of_le_of_lt (le_of_eq ?_) hN⟩
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.2 (Set.Ici_subset_Ici.2 (Nat.cast_nonneg N))]

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- `G` without the `e^{αT(ℓ)}` factor -/
noncomputable def g0 (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  {p : ℝ × Ω | Ev M ℓ B p.1 p.2}.indicator (fun p => ENNReal.ofReal (Real.exp (α * p.1))) (r, ω)

lemma measurable_g0 (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) : Measurable fun p : ℝ × Ω => g0 M α ℓ B p.1 p.2 := by
  unfold g0
  exact ((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).ennreal_ofReal).indicator
    (measurableSet_Ev M ℓ B hB)

lemma G_eq (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ) (ω : Ω) :
    G M α ℓ B r ω = ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) * g0 M α ℓ B r ω := by
  unfold G g0
  by_cases h : Ev M ℓ B r ω
  · rw [Set.indicator_of_mem (show ((r, ω) : ℝ × Ω) ∈ {p : ℝ × Ω | Ev M ℓ B p.1 p.2} from h),
      Set.indicator_of_mem (show ((r, ω) : ℝ × Ω) ∈ {p : ℝ × Ω | Ev M ℓ B p.1 p.2} from h),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]
  · rw [Set.indicator_of_notMem (show ((r, ω) : ℝ × Ω) ∉ {p : ℝ × Ω | Ev M ℓ B p.1 p.2} from h),
      Set.indicator_of_notMem (show ((r, ω) : ℝ × Ω) ∉ {p : ℝ × Ω | Ev M ℓ B p.1 p.2} from h),
      mul_zero]

lemma g0_neg (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ) (hr : r < 0)
    (ω : Ω) : g0 M α ℓ B r ω = 0 := by
  unfold g0
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨-, h0, -⟩
  exact absurd h0 (not_le.2 hr)

lemma g0_le (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ) (ω : Ω) :
    g0 M α ℓ B r ω ≤ ENNReal.ofReal (Real.exp (α * r)) := by
  unfold g0
  exact Set.indicator_le_self _ _ _

lemma G_zero (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ)
    (ω : Ω) (hω : ¬ M.T ℓ ω ≤ M.Γ ω) : G M α ℓ B r ω = 0 := by
  have := G_le M α hα ℓ B r ω
  rw [Set.indicator_of_notMem (show ω ∉ {ω | M.T ℓ ω ≤ M.Γ ω} from hω), zero_mul] at this
  exact le_antisymm this bot_le

lemma measurable_Hr2 (hγ : Measurable fun x : Path S => exitTime A x.1) (α : ℝ) :
    Measurable fun p : ℝ × (ℕ → Path S) => Hr (A := A) α p.1 p.2 := by
  unfold Hr
  have h0 : Measurable fun p : ℝ × (ℕ → Path S) => p.2 0 := (measurable_pi_apply 0).comp measurable_snd
  have hs : MeasurableSet {p : ℝ × (ℕ → Path S) | 0 ≤ p.1 ∧
      ENNReal.ofReal p.1 < min (exitTime A (p.2 0).1) (len (p.2 0))} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((hγ.comp h0).min (measurable_len.comp h0)))
  have e : (fun p : ℝ × (ℕ → Path S) => {x : ℕ → Path S | 0 ≤ p.1 ∧
      ENNReal.ofReal p.1 < min (exitTime A (x 0).1) (len (x 0))}.indicator
        (fun _ => ENNReal.ofReal (Real.exp (α * p.1))) p.2) =
      {p : ℝ × (ℕ → Path S) | 0 ≤ p.1 ∧
        ENNReal.ofReal p.1 < min (exitTime A (p.2 0).1) (len (p.2 0))}.indicator
        (fun p => ENNReal.ofReal (Real.exp (α * p.1))) := by
    funext p
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [e]
  exact ((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).ennreal_ofReal).indicator hs

/-- the averaged future-cycle factor `r ↦ e^{αr} Q(r < γ₁ ∧ τ₁)` (zero for `r < 0`) -/
noncomputable def hQ (α r : ℝ) : ℝ≥0∞ := ∫⁻ x, Hr (A := A) α r x ∂(M.Q.map (cyc M))

lemma measurable_hQ (α : ℝ) : Measurable (hQ M α) := by
  have := Q_finite' M
  exact (measurable_Hr2 M.exit_measurable α).lintegral_prod_right'

lemma hQ_neg (α r : ℝ) (hr : r < 0) : hQ M α r = 0 := by
  unfold hQ Hr
  refine (lintegral_congr fun x => Set.indicator_of_notMem ?_ _).trans lintegral_zero
  rintro ⟨h0, -⟩
  exact absurd h0 (not_le.2 hr)

lemma hQ_le {α : ℝ} {h : ℝ → ℝ} (hh : M.A4With α h) (r : ℝ) (hr : 0 ≤ r) :
    hQ M α r ≤ ENNReal.ofReal (h r) := by
  have := Q_finite' M
  unfold hQ
  rw [lintegral_Hr M α r hr]
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal (hh.2.2 r hr))
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- factorization over the future cycles (Definition 2 at `n = ℓ`) -/
lemma fact_j (hreg : M.IsWideSenseTabooRegen) (ℓ : ℕ) (f : ℝ × (ℕ → Path S) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, f ((M.T ℓ ω).toReal, cycj M ℓ ω) ∂M.P =
      ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, ∫⁻ x, f ((M.T ℓ ω).toReal, x) ∂(M.Q.map (cyc M)) ∂M.P := by
  have := M.isProb
  have := Q_finite' M
  have hg : Measurable fun ω => (M.T ℓ ω, cycj M ℓ ω) :=
    (M.measurable_T ℓ).prodMk (measurable_cycj M ℓ)
  have hf' : Measurable fun p : ℝ≥0∞ × (ℕ → Path S) => f (p.1.toReal, p.2) :=
    hf.comp (measurable_fst.ennreal_toReal.prodMk measurable_snd)
  calc _ = ∫⁻ p, f (p.1.toReal, p.2) ∂((M.P.restrict {ω | M.T ℓ ω ≤ M.Γ ω}).map
        fun ω => (M.T ℓ ω, cycj M ℓ ω)) := (lintegral_map hf' hg).symm
    _ = _ := by
        rw [prod_law_j M hreg ℓ, lintegral_prod _ hf'.aemeasurable,
          lintegral_map hf'.lintegral_prod_right' (M.measurable_T ℓ)]

/-- **cut factorization bound**: for a measurable cut `C`, at a fixed time `s` -/
lemma fact_s (hreg : M.IsWideSenseTabooRegen) (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ)
    (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (C : Set ℝ) (hC : MeasurableSet C) (s : ℝ) :
    ∫⁻ ω, C.indicator (fun r => G M α ℓ B r ω) (s - (M.T ℓ ω).toReal) ∂M.P ≤
      ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
        C.indicator (hQ M α) (s - (M.T ℓ ω).toReal) ∂M.P := by
  have hE := measurableSet_le_Γ M ℓ
  set f : ℝ × (ℕ → Path S) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (α * p.1)) * C.indicator (fun r => Hr (A := A) α r p.2) (s - p.1)
    with hfdef
  have hf : Measurable f := by
    refine (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).ennreal_ofReal.mul ?_
    have hm : Measurable fun p : ℝ × (ℕ → Path S) => (s - p.1, p.2) :=
      (measurable_const.sub measurable_fst).prodMk measurable_snd
    have e : (fun p : ℝ × (ℕ → Path S) => C.indicator (fun r => Hr (A := A) α r p.2) (s - p.1)) =
        fun p => ({q : ℝ × (ℕ → Path S) | q.1 ∈ C}.indicator
          (fun q => Hr (A := A) α q.1 q.2)) (s - p.1, p.2) := by
      funext p; rfl
    rw [e]
    exact ((measurable_Hr2 M.exit_measurable α).indicator (measurable_fst hC)).comp hm
  calc ∫⁻ ω, C.indicator (fun r => G M α ℓ B r ω) (s - (M.T ℓ ω).toReal) ∂M.P
      ≤ ∫⁻ ω, {ω | M.T ℓ ω ≤ M.Γ ω}.indicator
          (fun ω => f ((M.T ℓ ω).toReal, cycj M ℓ ω)) ω ∂M.P := by
        refine lintegral_mono fun ω => ?_
        by_cases hc : s - (M.T ℓ ω).toReal ∈ C
        · rw [Set.indicator_of_mem hc]
          refine (G_le M α hα ℓ B _ ω).trans (le_of_eq ?_)
          by_cases hω : ω ∈ {ω | M.T ℓ ω ≤ M.Γ ω}
          · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hfdef]
            simp only [Set.indicator_of_mem hc]
          · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
        · rw [Set.indicator_of_notMem hc]; exact bot_le
    _ = ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, ∫⁻ x, f ((M.T ℓ ω).toReal, x) ∂(M.Q.map (cyc M)) ∂M.P := by
        rw [lintegral_indicator hE]
        exact fact_j M hreg ℓ f hf
    _ = _ := by
        refine setLIntegral_congr_fun hE fun ω _ => ?_
        rw [hfdef]
        by_cases hc : s - (M.T ℓ ω).toReal ∈ C
        · simp only [Set.indicator_of_mem hc]
          rw [lintegral_const_mul _ (measurable_Hr M.exit_measurable α _), hQ]
        · simp only [Set.indicator_of_notMem hc, mul_zero, lintegral_zero]

end TabooRegen.UC

/-! ## ad51b63d glue, part 4 (L6b): pathwise good/bad case split -/
namespace TabooRegen.UC

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen TabooRegen.Twist

lemma conv_upper (U : Measure ℝ) (lam ε x0 t T : ℝ) (K : ℝ≥0∞) (b : ℝ → ℝ≥0∞)
    (hb0 : ∀ r, r < 0 → b r = 0) (hT : 0 ≤ T)
    (hukr : ∀ s, x0 ≤ s → (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) ≤
        ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) + ENNReal.ofReal ε)
    (hbad : t - x0 < T → (∫⁻ u in Set.Icc 0 t, b (t - T - u) ∂U) ≤ K) :
    (∫⁻ u in Set.Icc 0 t, b (t - T - u) ∂U) ≤ ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) +
      (ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => K) T) := by
  by_cases h : t - x0 < T
  · rw [Set.indicator_of_mem (show T ∈ Set.Ioi (t - x0) from h)]
    exact (hbad h).trans (le_add_left le_add_self)
  · rw [Set.indicator_of_notMem (show T ∉ Set.Ioi (t - x0) from h), add_zero,
      conv_shift U b hb0 (t - T) t (by linarith)]
    exact hukr _ (by linarith [not_lt.1 h])

lemma conv_lower (U : Measure ℝ) (lam ε x0 t T : ℝ) (K : ℝ≥0∞) (b : ℝ → ℝ≥0∞)
    (hb0 : ∀ r, r < 0 → b r = 0) (hT : 0 ≤ T)
    (hukr : ∀ s, x0 ≤ s → ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) ≤
        (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) + ENNReal.ofReal ε)
    (hbad : t - x0 < T → ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) ≤ K) :
    ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) ≤ (∫⁻ u in Set.Icc 0 t, b (t - T - u) ∂U) +
      (ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => K) T) := by
  by_cases h : t - x0 < T
  · rw [Set.indicator_of_mem (show T ∈ Set.Ioi (t - x0) from h)]
    exact (hbad h).trans (le_add_left le_add_self)
  · rw [Set.indicator_of_notMem (show T ∉ Set.Ioi (t - x0) from h), add_zero,
      conv_shift U b hb0 (t - T) t (by linarith)]
    exact hukr _ (by linarith [not_lt.1 h])

lemma conv_bad (U : Measure ℝ) (x0 t T : ℝ) (c : ℝ≥0∞) (b : ℝ → ℝ≥0∞)
    (hb0 : ∀ r, r < 0 → b r = 0) (hbc : ∀ r, b r ≤ c) (h : t - x0 < T) :
    (∫⁻ u in Set.Icc 0 t, b (t - T - u) ∂U) ≤ c * U (Set.Icc 0 x0) := by
  calc (∫⁻ u in Set.Icc 0 t, b (t - T - u) ∂U)
      ≤ ∫⁻ u, (Set.Icc 0 x0).indicator (fun _ => c) u ∂U := by
        rw [← lintegral_indicator measurableSet_Icc]
        refine lintegral_mono fun u => ?_
        by_cases hu : u ∈ Set.Icc 0 t
        · rw [Set.indicator_of_mem hu]
          by_cases hr : t - T - u < 0
          · rw [hb0 _ hr]; exact bot_le
          · have hu' : u ∈ Set.Icc 0 x0 := ⟨hu.1, by linarith [not_lt.1 hr]⟩
            rw [Set.indicator_of_mem hu']; exact hbc _
        · rw [Set.indicator_of_notMem hu]; exact bot_le
    _ = c * U (Set.Icc 0 x0) := lintegral_indicator_const measurableSet_Icc c

lemma int_bad (Mc : ℝ) (c : ℝ≥0∞) (b : ℝ → ℝ≥0∞) (hbc : ∀ r, b r ≤ c)
    (hbM : ∀ r, Mc ≤ r → b r = 0) :
    (∫⁻ r in Set.Ioi 0, b r) ≤ c * ENNReal.ofReal Mc := by
  calc (∫⁻ r in Set.Ioi 0, b r) ≤ ∫⁻ r, (Set.Ioo 0 Mc).indicator (fun _ => c) r := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_mono fun r => ?_
        by_cases hr : r ∈ Set.Ioi (0 : ℝ)
        · rw [Set.indicator_of_mem hr]
          by_cases hM : Mc ≤ r
          · rw [hbM r hM]; exact bot_le
          · rw [Set.indicator_of_mem (show r ∈ Set.Ioo 0 Mc from ⟨hr, not_le.1 hM⟩)]; exact hbc r
        · rw [Set.indicator_of_notMem hr]; exact bot_le
    _ = c * ENNReal.ofReal Mc := by
        rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, sub_zero]

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- the truncated normalized path function `r ↦ e^{αr} 1{event at lag r} 1{r < Mc}` -/
noncomputable def b1 (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (Mc : ℝ) (ω : Ω)
    (r : ℝ) : ℝ≥0∞ :=
  (Set.Iio Mc).indicator (fun r => g0 M α ℓ B r ω) r

lemma measurable_b1 (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) (Mc : ℝ) (ω : Ω) : Measurable (b1 M α ℓ B Mc ω) := by
  unfold b1
  exact ((measurable_g0 M α ℓ B hB).comp (measurable_id.prodMk measurable_const)).indicator
    measurableSet_Iio

lemma b1_neg (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (Mc : ℝ) (ω : Ω) (r : ℝ)
    (hr : r < 0) : b1 M α ℓ B Mc ω r = 0 := by
  unfold b1
  by_cases h : r ∈ Set.Iio Mc
  · rw [Set.indicator_of_mem h, g0_neg M α ℓ B r hr]
  · rw [Set.indicator_of_notMem h]

lemma b1_ge (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (Mc : ℝ) (ω : Ω) (r : ℝ)
    (hr : Mc ≤ r) : b1 M α ℓ B Mc ω r = 0 := by
  unfold b1
  exact Set.indicator_of_notMem (by simpa using hr) _

lemma b1_le (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (Mc : ℝ)
    (ω : Ω) (r : ℝ) : b1 M α ℓ B Mc ω r ≤ ENNReal.ofReal (Real.exp (α * Mc)) := by
  unfold b1
  by_cases h : r ∈ Set.Iio Mc
  · rw [Set.indicator_of_mem h]
    exact (g0_le M α ℓ B r ω).trans (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_of_lt h) hα)))
  · rw [Set.indicator_of_notMem h]; exact bot_le

lemma G1_eq (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (Mc : ℝ) (ω : Ω) (r : ℝ) :
    (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω) r =
      ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) * b1 M α ℓ B Mc ω r := by
  unfold b1
  by_cases h : r ∈ Set.Iio Mc
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, G_eq]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- **pathwise estimate on the truncated part** -/
lemma path1 (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) (U : Measure ℝ) (lam ε x0 t Mc : ℝ) (htot : ℝ → ℝ)
    (hukr : ∀ s, x0 ≤ s → ∀ b : ℝ → ℝ≥0∞, Measurable b →
      (∀ r, 0 ≤ r → b r ≤ ENNReal.ofReal (htot r)) →
      (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) ≤
          ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) + ENNReal.ofReal ε ∧
        ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) ≤
          (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) + ENNReal.ofReal ε)
    (hdom : ∀ r, 0 ≤ r → r < Mc → ENNReal.ofReal (Real.exp (α * r)) ≤ ENNReal.ofReal (htot r))
    (ω : Ω) :
    let eT := ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal))
    let K1 := ENNReal.ofReal (Real.exp (α * Mc)) *
      (U (Set.Icc 0 x0) + ENNReal.ofReal lam * ENNReal.ofReal Mc)
    let E := eT * (ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => K1) (M.T ℓ ω).toReal)
    (∫⁻ u in Set.Icc 0 t, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (t - u - (M.T ℓ ω).toReal) ∂U) ≤
      ENNReal.ofReal lam * (∫⁻ s in Set.Ioi 0, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (s - (M.T ℓ ω).toReal)) + E ∧
    ENNReal.ofReal lam * (∫⁻ s in Set.Ioi 0, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (s - (M.T ℓ ω).toReal)) ≤
      (∫⁻ u in Set.Icc 0 t, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (t - u - (M.T ℓ ω).toReal) ∂U) + E := by
  intro eT K1 E
  set T := (M.T ℓ ω).toReal with hTdef
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  set b := b1 M α ℓ B Mc ω with hbdef
  have hb := measurable_b1 M α ℓ B hB Mc ω
  have hb0 : ∀ r, r < 0 → b r = 0 := fun r hr => b1_neg M α ℓ B Mc ω r hr
  have hbc : ∀ r, b r ≤ ENNReal.ofReal (Real.exp (α * Mc)) := fun r => b1_le M α hα ℓ B Mc ω r
  have hbh : ∀ r, 0 ≤ r → b r ≤ ENNReal.ofReal (htot r) := by
    intro r hr
    by_cases hM : r < Mc
    · rw [hbdef, b1, Set.indicator_of_mem (show r ∈ Set.Iio Mc from hM)]
      exact (g0_le M α ℓ B r ω).trans (hdom r hr hM)
    · rw [hbdef, b1_ge M α ℓ B Mc ω r (not_lt.1 hM)]; exact bot_le
  have hc : (∫⁻ u in Set.Icc 0 t, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω) (t - u - T) ∂U) =
      eT * ∫⁻ u in Set.Icc 0 t, b (t - T - u) ∂U := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun u => ?_
    rw [G1_eq, sub_right_comm]
  have hy : (∫⁻ s in Set.Ioi 0, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω) (s - T)) =
      eT * ∫⁻ r in Set.Ioi 0, b r := by
    rw [← shift_Ioi b hb0 T hT, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun s => ?_
    rw [G1_eq]
  rw [hc, hy]
  have hK1a : ENNReal.ofReal (Real.exp (α * Mc)) * U (Set.Icc 0 x0) ≤ K1 :=
    mul_le_mul_right le_self_add _
  have hK1b : ENNReal.ofReal lam * (ENNReal.ofReal (Real.exp (α * Mc)) * ENNReal.ofReal Mc) ≤ K1 := by
    calc ENNReal.ofReal lam * (ENNReal.ofReal (Real.exp (α * Mc)) * ENNReal.ofReal Mc)
        = ENNReal.ofReal (Real.exp (α * Mc)) * (ENNReal.ofReal lam * ENNReal.ofReal Mc) := by ring
      _ ≤ K1 := mul_le_mul_right le_add_self _
  have hup := conv_upper U lam ε x0 t T K1 b hb0 hT (fun s hs => (hukr s hs b hb hbh).1)
    (fun h => (conv_bad U x0 t T _ b hb0 hbc h).trans hK1a)
  have hlo := conv_lower U lam ε x0 t T K1 b hb0 hT (fun s hs => (hukr s hs b hb hbh).2)
    (fun _ => (mul_le_mul_right (int_bad Mc _ b hbc (fun r hr => b1_ge M α ℓ B Mc ω r hr)) _).trans
      hK1b)
  constructor
  · calc eT * ∫⁻ u in Set.Icc 0 t, b (t - T - u) ∂U
        ≤ eT * (ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) +
            (ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => K1) T)) :=
          mul_le_mul_right hup _
      _ = ENNReal.ofReal lam * (eT * ∫⁻ r in Set.Ioi 0, b r) + E := by
          simp only [E]; ring
  · calc ENNReal.ofReal lam * (eT * ∫⁻ r in Set.Ioi 0, b r)
        = eT * (ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r)) := by ring
      _ ≤ eT * ((∫⁻ u in Set.Icc 0 t, b (t - T - u) ∂U) +
            (ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => K1) T)) :=
          mul_le_mul_right hlo _
      _ = (eT * ∫⁻ u in Set.Icc 0 t, b (t - T - u) ∂U) + E := by
          simp only [E]; ring

end TabooRegen.UC

/-! ## ad51b63d glue, part 5 (L6c): integrated bounds D7/D8 -/
namespace TabooRegen.UC

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen TabooRegen.Twist

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

lemma K_eval (α : ℝ) (ℓ : ℕ)
    (hD : ((M.P.restrict {ω | M.T ℓ ω ≤ M.Γ ω}).map fun ω => (M.T ℓ ω).toReal).withDensity
        (fun u => ENNReal.ofReal (Real.exp (α * u))) = QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ)
    (hprob : QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ Set.univ = 1) (c K' : ℝ≥0∞) (x : ℝ) :
    K M α ℓ (fun v => c + (Set.Ioi x).indicator (fun _ => K') v) =
      c + K' * QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ (Set.Ioi x) := by
  rw [← lintegral_L M α ℓ (f := fun v => c + (Set.Ioi x).indicator (fun _ => K') v)
    (by exact measurable_const.add (measurable_const.indicator measurableSet_Ioi)), hD,
    lintegral_add_left measurable_const, lintegral_const, hprob, mul_one,
    lintegral_indicator_const measurableSet_Ioi]

lemma K_const (α : ℝ) (ℓ : ℕ)
    (hD : ((M.P.restrict {ω | M.T ℓ ω ≤ M.Γ ω}).map fun ω => (M.T ℓ ω).toReal).withDensity
        (fun u => ENNReal.ofReal (Real.exp (α * u))) = QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ)
    (hprob : QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ Set.univ = 1) (c : ℝ≥0∞) :
    K M α ℓ (fun _ => c) = c := by
  rw [← lintegral_L M α ℓ (f := fun _ => c) measurable_const, hD, lintegral_const, hprob, mul_one]

lemma measurable_GC (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) (C : Set ℝ) (hC : MeasurableSet C) :
    Measurable fun p : ℝ × Ω => C.indicator (fun r => G M α ℓ B r p.2) p.1 := by
  have := (measurable_G M α ℓ B hB).indicator (measurable_fst hC)
  convert this using 1
  funext p
  by_cases h : p.1 ∈ C
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' C from h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' C from h)]

lemma zero_off (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (C : Set ℝ) (ω : Ω) (hω : ω ∉ {ω | M.T ℓ ω ≤ M.Γ ω}) (r : ℝ) :
    C.indicator (fun r => G M α ℓ B r ω) r = 0 := by
  by_cases h : r ∈ C
  · rw [Set.indicator_of_mem h]; exact G_zero M α hα ℓ B r ω hω
  · rw [Set.indicator_of_notMem h]

lemma restrict_eq (ℓ : ℕ) (f : Ω → ℝ≥0∞) (hf : ∀ ω, ω ∉ {ω | M.T ℓ ω ≤ M.Γ ω} → f ω = 0) :
    ∫⁻ ω, f ω ∂M.P = ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, f ω ∂M.P := by
  refine (setLIntegral_eq_of_support_subset ?_).symm
  intro ω hω
  by_contra hn
  exact hω (hf ω hn)

lemma measurable_eT (α : ℝ) (ℓ : ℕ) :
    Measurable fun ω => ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) :=
  (Real.measurable_exp.comp (measurable_const.mul (M.measurable_T ℓ).ennreal_toReal)).ennreal_ofReal

/-- **D7**: integrated two-sided bound on the truncated part -/
lemma int1 (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) (U : Measure ℝ) (lam ε x0 t Mc : ℝ) (htot : ℝ → ℝ)
    (hukr : ∀ s, x0 ≤ s → ∀ b : ℝ → ℝ≥0∞, Measurable b →
      (∀ r, 0 ≤ r → b r ≤ ENNReal.ofReal (htot r)) →
      (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) ≤
          ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) + ENNReal.ofReal ε ∧
        ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) ≤
          (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) + ENNReal.ofReal ε)
    (hdom : ∀ r, 0 ≤ r → r < Mc → ENNReal.ofReal (Real.exp (α * r)) ≤ ENNReal.ofReal (htot r))
    (K1 : ℝ≥0∞)
    (hK1 : K1 = ENNReal.ofReal (Real.exp (α * Mc)) *
      (U (Set.Icc 0 x0) + ENNReal.ofReal lam * ENNReal.ofReal Mc)) :
    (∫⁻ ω, ∫⁻ u in Set.Icc 0 t, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (t - u - (M.T ℓ ω).toReal) ∂U ∂M.P) ≤
      ENNReal.ofReal lam * (∫⁻ ω, (∫⁻ s in Set.Ioi 0, (Set.Iio Mc).indicator
        (fun r => G M α ℓ B r ω) (s - (M.T ℓ ω).toReal)) ∂M.P) +
        K M α ℓ (fun v => ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => K1) v) ∧
    ENNReal.ofReal lam * (∫⁻ ω, (∫⁻ s in Set.Ioi 0, (Set.Iio Mc).indicator
        (fun r => G M α ℓ B r ω) (s - (M.T ℓ ω).toReal)) ∂M.P) ≤
      (∫⁻ ω, ∫⁻ u in Set.Icc 0 t, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (t - u - (M.T ℓ ω).toReal) ∂U ∂M.P) +
        K M α ℓ (fun v => ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => K1) v) := by
  subst hK1
  have hEm : Measurable fun ω => ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
      (ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => ENNReal.ofReal (Real.exp (α * Mc)) *
      (U (Set.Icc 0 x0) + ENNReal.ofReal lam * ENNReal.ofReal Mc)) (M.T ℓ ω).toReal) :=
    (measurable_eT M α ℓ).mul
      (((measurable_const.indicator measurableSet_Ioi).comp (M.measurable_T ℓ).ennreal_toReal).const_add _)
  have hX := restrict_eq M ℓ (fun ω => ∫⁻ u in Set.Icc 0 t, (Set.Iio Mc).indicator
      (fun r => G M α ℓ B r ω) (t - u - (M.T ℓ ω).toReal) ∂U)
    (fun ω hω => by simp only [zero_off M α hα ℓ B _ ω hω, lintegral_zero])
  have hY := restrict_eq M ℓ (fun ω => ∫⁻ s in Set.Ioi 0, (Set.Iio Mc).indicator
      (fun r => G M α ℓ B r ω) (s - (M.T ℓ ω).toReal))
    (fun ω hω => by simp only [zero_off M α hα ℓ B _ ω hω, lintegral_zero])
  have hp := fun ω => path1 M α hα ℓ B hB U lam ε x0 t Mc htot hukr hdom ω
  rw [hX, hY]
  constructor
  · calc _ ≤ ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, (ENNReal.ofReal lam * (∫⁻ s in Set.Ioi 0,
          (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω) (s - (M.T ℓ ω).toReal)) +
          ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
          (ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => ENNReal.ofReal (Real.exp (α * Mc)) *
          (U (Set.Icc 0 x0) + ENNReal.ofReal lam * ENNReal.ofReal Mc)) (M.T ℓ ω).toReal)) ∂M.P :=
          lintegral_mono fun ω => (hp ω).1
      _ = _ := by
          rw [lintegral_add_right _ hEm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rfl
  · calc _ = ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, ENNReal.ofReal lam * (∫⁻ s in Set.Ioi 0,
          (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω) (s - (M.T ℓ ω).toReal)) ∂M.P :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, ((∫⁻ u in Set.Icc 0 t, (Set.Iio Mc).indicator
          (fun r => G M α ℓ B r ω) (t - u - (M.T ℓ ω).toReal) ∂U) +
          ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
          (ENNReal.ofReal ε + (Set.Ioi (t - x0)).indicator (fun _ => ENNReal.ofReal (Real.exp (α * Mc)) *
          (U (Set.Icc 0 x0) + ENNReal.ofReal lam * ENNReal.ofReal Mc)) (M.T ℓ ω).toReal)) ∂M.P :=
          lintegral_mono fun ω => (hp ω).2
      _ = _ := by
          rw [lintegral_add_right _ hEm]
          rfl

lemma hQC_le {α : ℝ} {hA : ℝ → ℝ} (hAw : M.A4With α hA) (C : Set ℝ) (r : ℝ) (hr : 0 ≤ r) :
    C.indicator (hQ M α) r ≤ ENNReal.ofReal (hA r) := by
  by_cases h : r ∈ C
  · rw [Set.indicator_of_mem h]; exact hQ_le M hAw r hr
  · rw [Set.indicator_of_notMem h]; exact bot_le

lemma hQC_neg (α : ℝ) (C : Set ℝ) (r : ℝ) (hr : r < 0) : C.indicator (hQ M α) r = 0 := by
  by_cases h : r ∈ C
  · rw [Set.indicator_of_mem h]; exact hQ_neg M α r hr
  · rw [Set.indicator_of_notMem h]

/-- **D8 (X part)**: the cut part of the convolution -/
lemma int2 (hreg : M.IsWideSenseTabooRegen) (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ)
    (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (hB : MeasurableSet B)
    (U : Measure ℝ) [SFinite U] (lam ε x0 t Mc : ℝ) (htot hA : ℝ → ℝ) (hAw : M.A4With α hA)
    (hle : ∀ r, 0 ≤ r → hA r ≤ htot r)
    (hukr : ∀ s, x0 ≤ s → ∀ b : ℝ → ℝ≥0∞, Measurable b →
      (∀ r, 0 ≤ r → b r ≤ ENNReal.ofReal (htot r)) →
      (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) ≤
          ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) + ENNReal.ofReal ε ∧
        ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) ≤
          (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) + ENNReal.ofReal ε) :
    (∫⁻ ω, ∫⁻ u in Set.Icc 0 t, (Set.Ici Mc).indicator (fun r => G M α ℓ B r ω)
        (t - u - (M.T ℓ ω).toReal) ∂U ∂M.P) ≤
      K M α ℓ (fun v => (ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, (Set.Ici Mc).indicator (hQ M α) r) +
        ENNReal.ofReal ε) + (Set.Ioi (t - x0)).indicator
          (fun _ => ENNReal.ofReal (hA 0) * U (Set.Icc 0 x0)) v) := by
  have : IsProbabilityMeasure M.P := M.isProb
  have hC : MeasurableSet (Set.Ici Mc) := measurableSet_Ici
  have hT := (M.measurable_T ℓ).ennreal_toReal
  have hGC := measurable_GC M α ℓ B hB (Set.Ici Mc) hC
  have hF : Measurable fun p : Ω × ℝ => (Set.Ici Mc).indicator (fun r => G M α ℓ B r p.1)
      (t - p.2 - (M.T ℓ p.1).toReal) :=
    hGC.comp (((measurable_const.sub measurable_snd).sub (hT.comp measurable_fst)).prodMk
      measurable_fst)
  have hbm : Measurable ((Set.Ici Mc).indicator (hQ M α)) := (measurable_hQ M α).indicator hC
  have hF2 : Measurable fun p : ℝ × Ω => ENNReal.ofReal (Real.exp (α * (M.T ℓ p.2).toReal)) *
      (Set.Ici Mc).indicator (hQ M α) (t - p.1 - (M.T ℓ p.2).toReal) :=
    ((measurable_eT M α ℓ).comp measurable_snd).mul
      (hbm.comp ((measurable_const.sub measurable_fst).sub (hT.comp measurable_snd)))
  have hb0 := hQC_neg M α (Set.Ici Mc)
  have hbh : ∀ r, 0 ≤ r → (Set.Ici Mc).indicator (hQ M α) r ≤ ENNReal.ofReal (htot r) :=
    fun r hr => (hQC_le M hAw _ r hr).trans (ENNReal.ofReal_le_ofReal (hle r hr))
  have hbc : ∀ r, (Set.Ici Mc).indicator (hQ M α) r ≤ ENNReal.ofReal (hA 0) := by
    intro r
    by_cases hr : r < 0
    · rw [hb0 r hr]; exact bot_le
    · have hr' : 0 ≤ r := not_lt.1 hr
      exact (hQC_le M hAw _ r hr').trans (ENNReal.ofReal_le_ofReal
        (hAw.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hr') hr'))
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc _ ≤ ∫⁻ u in Set.Icc 0 t, ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω},
          ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
          (Set.Ici Mc).indicator (hQ M α) (t - u - (M.T ℓ ω).toReal) ∂M.P ∂U :=
        lintegral_mono fun u => fact_s M hreg α hα ℓ B (Set.Ici Mc) hC (t - u)
    _ = ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, ∫⁻ u in Set.Icc 0 t,
          ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
          (Set.Ici Mc).indicator (hQ M α) (t - u - (M.T ℓ ω).toReal) ∂U ∂M.P :=
        lintegral_lintegral_swap hF2.aemeasurable
    _ = ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
          (∫⁻ u in Set.Icc 0 t, (Set.Ici Mc).indicator (hQ M α) (t - (M.T ℓ ω).toReal - u) ∂U)
          ∂M.P := by
        refine lintegral_congr fun ω => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun u => ?_
        rw [sub_right_comm]
    _ ≤ _ := by
        refine lintegral_mono fun ω => mul_le_mul_right ?_ _
        exact (conv_upper U lam ε x0 t (M.T ℓ ω).toReal _ _ hb0 ENNReal.toReal_nonneg
          (fun s hs => (hukr s hs _ hbm hbh).1)
          (fun h => conv_bad U x0 t _ _ _ hb0 hbc h)).trans (le_of_eq (add_assoc _ _ _).symm)

/-- **D8 (Y part)** -/
lemma int2y (hreg : M.IsWideSenseTabooRegen) (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ)
    (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (hB : MeasurableSet B) (Mc : ℝ) :
    (∫⁻ ω, (∫⁻ s in Set.Ioi 0, (Set.Ici Mc).indicator (fun r => G M α ℓ B r ω)
        (s - (M.T ℓ ω).toReal)) ∂M.P) ≤
      K M α ℓ (fun _ => ∫⁻ r in Set.Ioi 0, (Set.Ici Mc).indicator (hQ M α) r) := by
  have : IsProbabilityMeasure M.P := M.isProb
  have hC : MeasurableSet (Set.Ici Mc) := measurableSet_Ici
  have hT := (M.measurable_T ℓ).ennreal_toReal
  have hGC := measurable_GC M α ℓ B hB (Set.Ici Mc) hC
  have hF : Measurable fun p : Ω × ℝ => (Set.Ici Mc).indicator (fun r => G M α ℓ B r p.1)
      (p.2 - (M.T ℓ p.1).toReal) :=
    hGC.comp ((measurable_snd.sub (hT.comp measurable_fst)).prodMk measurable_fst)
  have hbm : Measurable ((Set.Ici Mc).indicator (hQ M α)) := (measurable_hQ M α).indicator hC
  have hF2 : Measurable fun p : ℝ × Ω => ENNReal.ofReal (Real.exp (α * (M.T ℓ p.2).toReal)) *
      (Set.Ici Mc).indicator (hQ M α) (p.1 - (M.T ℓ p.2).toReal) :=
    ((measurable_eT M α ℓ).comp measurable_snd).mul
      (hbm.comp (measurable_fst.sub (hT.comp measurable_snd)))
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc _ ≤ ∫⁻ s in Set.Ioi 0, ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω},
          ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
          (Set.Ici Mc).indicator (hQ M α) (s - (M.T ℓ ω).toReal) ∂M.P :=
        lintegral_mono fun s => fact_s M hreg α hα ℓ B (Set.Ici Mc) hC s
    _ = ∫⁻ ω in {ω | M.T ℓ ω ≤ M.Γ ω}, (∫⁻ s in Set.Ioi 0,
          ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
          (Set.Ici Mc).indicator (hQ M α) (s - (M.T ℓ ω).toReal)) ∂M.P :=
        lintegral_lintegral_swap hF2.aemeasurable
    _ = _ := by
        refine lintegral_congr fun ω => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          shift_Ioi _ (hQC_neg M α (Set.Ici Mc)) _ ENNReal.toReal_nonneg]
        rfl

end TabooRegen.UC

/-! ## ad51b63d glue, part 6 (L7): assembly D9 -/
namespace TabooRegen.UC

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen TabooRegen.Twist
  TabooRegen.Prop2

lemma split_ind (f : ℝ → ℝ≥0∞) (Mc r : ℝ) :
    f r = (Set.Iio Mc).indicator f r + (Set.Ici Mc).indicator f r := by
  by_cases h : r < Mc
  · rw [Set.indicator_of_mem (show r ∈ Set.Iio Mc from h),
      Set.indicator_of_notMem (show r ∉ Set.Ici Mc from not_le.2 h), add_zero]
  · rw [Set.indicator_of_notMem (show r ∉ Set.Iio Mc from h),
      Set.indicator_of_mem (show r ∈ Set.Ici Mc from not_lt.1 h), zero_add]

lemma arith (X1 X2 Y1 Y2 L e K0 K1 c I2 : ℝ≥0∞) (h1u : X1 ≤ L * Y1 + (e + K1 * c))
    (h1l : L * Y1 ≤ X1 + (e + K1 * c)) (h2 : X2 ≤ L * I2 + e + K0 * c) (h3 : Y2 ≤ I2)
    (hI2 : L * I2 ≤ e) (hct : (K0 + K1) * c ≤ e) :
    X1 + X2 ≤ L * (Y1 + Y2) + (e + e + e + e) ∧ L * (Y1 + Y2) ≤ X1 + X2 + (e + e + e + e) := by
  have hK1 : K1 * c ≤ e := le_trans (mul_le_mul' le_add_self le_rfl) hct
  constructor
  · calc X1 + X2 ≤ (L * Y1 + (e + K1 * c)) + (L * I2 + e + K0 * c) := add_le_add h1u h2
      _ = L * Y1 + e + e + L * I2 + (K0 + K1) * c := by ring
      _ ≤ L * (Y1 + Y2) + e + e + e + e :=
          add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul' le_rfl le_self_add) le_rfl)
            le_rfl) hI2) hct
      _ = L * (Y1 + Y2) + (e + e + e + e) := by ring
  · calc L * (Y1 + Y2) = L * Y1 + L * Y2 := mul_add _ _ _
      _ ≤ (X1 + (e + K1 * c)) + L * I2 := add_le_add h1l (mul_le_mul' le_rfl h3)
      _ ≤ (X1 + X2 + (e + e)) + e :=
          add_le_add (add_le_add le_self_add (add_le_add le_rfl hK1)) hI2
      _ = X1 + X2 + (e + e + e) := by ring
      _ ≤ X1 + X2 + (e + e + e + e) := add_le_add le_rfl le_self_add

lemma abs_le_two (X Y : ℝ≥0∞) (lam ε : ℝ) (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hY : Y ≠ ⊤)
    (h1 : X ≤ ENNReal.ofReal lam * Y + ENNReal.ofReal ε)
    (h2 : ENNReal.ofReal lam * Y ≤ X + ENNReal.ofReal ε) :
    |X.toReal - lam * Y.toReal| ≤ ε := by
  have hLY : ENNReal.ofReal lam * Y ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY
  have hS : ENNReal.ofReal lam * Y + ENNReal.ofReal ε ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hLY, ENNReal.ofReal_ne_top⟩
  have hX : X ≠ ⊤ := ne_top_of_le_ne_top hS h1
  have h1' := (ENNReal.toReal_le_toReal hX hS).2 h1
  have h2' := (ENNReal.toReal_le_toReal hLY (ENNReal.add_ne_top.2 ⟨hX, ENNReal.ofReal_ne_top⟩)).2 h2
  rw [ENNReal.toReal_add hLY ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam,
    ENNReal.toReal_ofReal hε] at h1'
  rw [ENNReal.toReal_add hX ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam,
    ENNReal.toReal_ofReal hε] at h2'
  rw [abs_le]; constructor <;> linarith

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

lemma G_neg (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (r : ℝ) (hr : r < 0)
    (ω : Ω) : G M α ℓ B r ω = 0 := by
  rw [G_eq, g0_neg M α ℓ B r hr, mul_zero]

lemma btilde_nonneg (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (s : ℝ) :
    0 ≤ M.btilde α ℓ B s := by
  unfold Model.btilde; exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg

lemma btilde_eq (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (hB : MeasurableSet B)
    (s : ℝ) (hs : 0 ≤ s) :
    M.btilde α ℓ B s = (∫⁻ ω, G M α ℓ B (s - (M.T ℓ ω).toReal) ω ∂M.P).toReal := by
  rw [← btilde_rep M α ℓ B hB s hs, ENNReal.toReal_ofReal (btilde_nonneg M α ℓ B s)]

lemma measurable_bt (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) :
    Measurable fun s => (∫⁻ ω, G M α ℓ B (s - (M.T ℓ ω).toReal) ω ∂M.P).toReal := by
  have : IsProbabilityMeasure M.P := M.isProb
  have hT := (M.measurable_T ℓ).ennreal_toReal
  have hm : Measurable fun p : ℝ × Ω => G M α ℓ B (p.1 - (M.T ℓ p.2).toReal) p.2 :=
    (measurable_G M α ℓ B hB).comp ((measurable_fst.sub (hT.comp measurable_snd)).prodMk
      measurable_snd)
  exact hm.lintegral_prod_right'.ennreal_toReal

lemma int_Ioi_eq (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) :
    ∫ s in Set.Ioi 0, M.btilde α ℓ B s =
      (∫⁻ ω, (∫⁻ s in Set.Ioi 0, G M α ℓ B (s - (M.T ℓ ω).toReal) ω) ∂M.P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => btilde_nonneg M α ℓ B s)
    ((measurable_bt M α ℓ B hB).aestronglyMeasurable.congr
      ((ae_restrict_mem measurableSet_Ioi).mono fun s hs =>
        (btilde_eq M α ℓ B hB s (le_of_lt hs)).symm)),
    int_rep M α ℓ B hB]

lemma int_Icc_eq (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) (U : Measure ℝ) [SFinite U] (t : ℝ) :
    ∫ u in Set.Icc 0 t, M.btilde α ℓ B (t - u) ∂U =
      (∫⁻ ω, ∫⁻ u in Set.Icc 0 t, G M α ℓ B (t - u - (M.T ℓ ω).toReal) ω ∂U ∂M.P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u => btilde_nonneg M α ℓ B (t - u))
    (((measurable_bt M α ℓ B hB).comp (measurable_const.sub measurable_id)).aestronglyMeasurable.congr
      ((ae_restrict_mem measurableSet_Icc).mono fun u hu =>
        (btilde_eq M α ℓ B hB (t - u) (by linarith [hu.2])).symm)),
    conv_rep M α ℓ B hB U t]

lemma I2_le {α : ℝ} {hA : ℝ → ℝ} (hAw : M.A4With α hA) (Mc : ℝ) (hMc : 0 ≤ Mc) :
    ∫⁻ r in Set.Ioi 0, (Set.Ici Mc).indicator (hQ M α) r ≤
      ∫⁻ r in Set.Ici Mc, ENNReal.ofReal (hA r) := by
  rw [← lintegral_indicator measurableSet_Ici]
  refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun r => ?_)
  by_cases h : r ∈ Set.Ici Mc
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; exact hQ_le M hAw r (le_trans hMc h)
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

lemma Y_lt_top (hreg : M.IsWideSenseTabooRegen) (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ)
    (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (hB : MeasurableSet B)
    (hD : ((M.P.restrict {ω | M.T ℓ ω ≤ M.Γ ω}).map fun ω => (M.T ℓ ω).toReal).withDensity
        (fun u => ENNReal.ofReal (Real.exp (α * u))) = QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ)
    (hprob : QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ Set.univ = 1)
    {hA : ℝ → ℝ} (hAw : M.A4With α hA) :
    (∫⁻ ω, (∫⁻ s in Set.Ioi 0, G M α ℓ B (s - (M.T ℓ ω).toReal) ω) ∂M.P) < ⊤ := by
  have h := int2y M hreg α hα ℓ B hB 0
  rw [K_const M α ℓ hD hprob] at h
  have he : (∫⁻ ω, (∫⁻ s in Set.Ioi 0, G M α ℓ B (s - (M.T ℓ ω).toReal) ω) ∂M.P) =
      ∫⁻ ω, (∫⁻ s in Set.Ioi 0, (Set.Ici 0).indicator (fun r => G M α ℓ B r ω)
        (s - (M.T ℓ ω).toReal)) ∂M.P := by
    refine lintegral_congr fun ω => lintegral_congr fun s => ?_
    by_cases hs : s - (M.T ℓ ω).toReal < 0
    · rw [G_neg M α ℓ B _ hs, Set.indicator_of_notMem
        (show s - (M.T ℓ ω).toReal ∉ Set.Ici (0:ℝ) from not_le.2 hs)]
    · rw [Set.indicator_of_mem (show s - (M.T ℓ ω).toReal ∈ Set.Ici (0:ℝ) from not_lt.1 hs)]
  rw [he]
  exact lt_of_le_of_lt (h.trans (I2_le M hAw 0 le_rfl)) (Integrable.lintegral_lt_top hAw.2.1)

/-- **D9 (ENNReal form, fixed `t`)** -/
lemma assemble (hreg : M.IsWideSenseTabooRegen) (α : ℝ) (hα : 0 ≤ α) (ℓ : ℕ)
    (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (hB : MeasurableSet B)
    (U : Measure ℝ) [SFinite U] (lam ε x0 t Mc : ℝ) (htot hA : ℝ → ℝ) (hAw : M.A4With α hA)
    (hle : ∀ r, 0 ≤ r → hA r ≤ htot r)
    (hukr : ∀ s, x0 ≤ s → ∀ b : ℝ → ℝ≥0∞, Measurable b →
      (∀ r, 0 ≤ r → b r ≤ ENNReal.ofReal (htot r)) →
      (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) ≤
          ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) + ENNReal.ofReal ε ∧
        ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) ≤
          (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) + ENNReal.ofReal ε)
    (hdom : ∀ r, 0 ≤ r → r < Mc → ENNReal.ofReal (Real.exp (α * r)) ≤ ENNReal.ofReal (htot r))
    (hD : ((M.P.restrict {ω | M.T ℓ ω ≤ M.Γ ω}).map fun ω => (M.T ℓ ω).toReal).withDensity
        (fun u => ENNReal.ofReal (Real.exp (α * u))) = QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ)
    (hprob : QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ Set.univ = 1)
    (hI2 : ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, (Set.Ici Mc).indicator (hQ M α) r) ≤
      ENNReal.ofReal ε)
    (hct : (ENNReal.ofReal (hA 0) * U (Set.Icc 0 x0) + ENNReal.ofReal (Real.exp (α * Mc)) *
      (U (Set.Icc 0 x0) + ENNReal.ofReal lam * ENNReal.ofReal Mc)) *
        QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ (Set.Ioi (t - x0)) ≤ ENNReal.ofReal ε) :
    (∫⁻ ω, ∫⁻ u in Set.Icc 0 t, G M α ℓ B (t - u - (M.T ℓ ω).toReal) ω ∂U ∂M.P) ≤
      ENNReal.ofReal lam * (∫⁻ ω, (∫⁻ s in Set.Ioi 0, G M α ℓ B (s - (M.T ℓ ω).toReal) ω) ∂M.P) +
        (ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε) ∧
    ENNReal.ofReal lam * (∫⁻ ω, (∫⁻ s in Set.Ioi 0, G M α ℓ B (s - (M.T ℓ ω).toReal) ω) ∂M.P) ≤
      (∫⁻ ω, ∫⁻ u in Set.Icc 0 t, G M α ℓ B (t - u - (M.T ℓ ω).toReal) ω ∂U ∂M.P) +
        (ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε) := by
  have : IsProbabilityMeasure M.P := M.isProb
  have hT := (M.measurable_T ℓ).ennreal_toReal
  have h1 := int1 M α hα ℓ B hB U lam ε x0 t Mc htot hukr hdom _ rfl
  rw [K_eval M α ℓ hD hprob] at h1
  have h2 := int2 M hreg α hα ℓ B hB U lam ε x0 t Mc htot hA hAw hle hukr
  rw [K_eval M α ℓ hD hprob] at h2
  have h3 := int2y M hreg α hα ℓ B hB Mc
  rw [K_const M α ℓ hD hprob] at h3
  have hmX : ∀ C : Set ℝ, MeasurableSet C → Measurable fun p : Ω × ℝ =>
      C.indicator (fun r => G M α ℓ B r p.1) (t - p.2 - (M.T ℓ p.1).toReal) := fun C hC =>
    (measurable_GC M α ℓ B hB C hC).comp
      (((measurable_const.sub measurable_snd).sub (hT.comp measurable_fst)).prodMk measurable_fst)
  have hmY : ∀ C : Set ℝ, MeasurableSet C → Measurable fun p : Ω × ℝ =>
      C.indicator (fun r => G M α ℓ B r p.1) (p.2 - (M.T ℓ p.1).toReal) := fun C hC =>
    (measurable_GC M α ℓ B hB C hC).comp
      ((measurable_snd.sub (hT.comp measurable_fst)).prodMk measurable_fst)
  have hX1m : Measurable fun ω => ∫⁻ u in Set.Icc 0 t, (Set.Iio Mc).indicator
      (fun r => G M α ℓ B r ω) (t - u - (M.T ℓ ω).toReal) ∂U :=
    (hmX _ measurableSet_Iio).lintegral_prod_right'
  have hY1m : Measurable fun ω => ∫⁻ s in Set.Ioi 0, (Set.Iio Mc).indicator
      (fun r => G M α ℓ B r ω) (s - (M.T ℓ ω).toReal) :=
    (hmY _ measurableSet_Iio).lintegral_prod_right'
  have hXe : (∫⁻ ω, ∫⁻ u in Set.Icc 0 t, G M α ℓ B (t - u - (M.T ℓ ω).toReal) ω ∂U ∂M.P) =
      (∫⁻ ω, ∫⁻ u in Set.Icc 0 t, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (t - u - (M.T ℓ ω).toReal) ∂U ∂M.P) +
      (∫⁻ ω, ∫⁻ u in Set.Icc 0 t, (Set.Ici Mc).indicator (fun r => G M α ℓ B r ω)
        (t - u - (M.T ℓ ω).toReal) ∂U ∂M.P) := by
    rw [← lintegral_add_left hX1m]
    refine lintegral_congr fun ω => ?_
    have hf : Measurable fun u => (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (t - u - (M.T ℓ ω).toReal) := (hmX _ measurableSet_Iio).comp measurable_prodMk_left
    rw [← lintegral_add_left hf]
    exact lintegral_congr fun u => split_ind (fun r => G M α ℓ B r ω) Mc _
  have hYe : (∫⁻ ω, (∫⁻ s in Set.Ioi 0, G M α ℓ B (s - (M.T ℓ ω).toReal) ω) ∂M.P) =
      (∫⁻ ω, (∫⁻ s in Set.Ioi 0, (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (s - (M.T ℓ ω).toReal)) ∂M.P) +
      (∫⁻ ω, (∫⁻ s in Set.Ioi 0, (Set.Ici Mc).indicator (fun r => G M α ℓ B r ω)
        (s - (M.T ℓ ω).toReal)) ∂M.P) := by
    rw [← lintegral_add_left hY1m]
    refine lintegral_congr fun ω => ?_
    have hf : Measurable fun s => (Set.Iio Mc).indicator (fun r => G M α ℓ B r ω)
        (s - (M.T ℓ ω).toReal) := (hmY _ measurableSet_Iio).comp measurable_prodMk_left
    rw [← lintegral_add_left hf]
    exact lintegral_congr fun s => split_ind (fun r => G M α ℓ B r ω) Mc _
  rw [hXe, hYe]
  exact arith _ _ _ _ _ _ _ _ _ _ h1.1 h1.2 h2 h3 hI2 hct

end TabooRegen.UC

namespace TabooRegen.UC

open TabooRegen TabooRegen.Model TabooRegen.DelayShift TabooRegen.Regen TabooRegen.Twist
  TabooRegen.Prop2

/-- **uniform convergence of (4.2)**, from the uniform key renewal theorem, the renewal
decomposition and the Chernoff tail bound (taken as hypotheses). -/
theorem uc_core {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S} {Ω : Type*}
    [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h3 : M.A3 α) (h4 : M.A4 α) (k : ℝ → ℕ)
    (hkg : ∃ c < M.rate α, ∀ᶠ t in atTop, (k t : ℝ) ≤ c * t)
    (hUKR : ∀ h : ℝ → ℝ, AntitoneOn h (Set.Ici 0) → IntegrableOn h (Set.Ici 0) →
      ∀ ε > 0, ∀ᶠ t in atTop, ∀ b : ℝ → ℝ, Measurable b → (∀ s, 0 ≤ s → |b s| ≤ h s) →
      |∫ s in Set.Icc 0 t, b (t - s)
          ∂(SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) (M.Gtilde α)) -
        (SmithRegenerative.Equilibrium.mean (M.Gtilde α)).toReal⁻¹ * ∫ s in Set.Ioi 0, b s| ≤ ε)
    (hdec1 : ∀ (ℓ : ℕ) (t : ℝ), 0 ≤ t → ∀ B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ),
      MeasurableSet B →
      Real.exp (α * t) * (M.P {ω | ℓ < M.strad t ω ∧ (M.win ℓ t ω, M.age t ω) ∈ B ∧
          ENNReal.ofReal t < M.Γ ω}).toReal =
      ∫ u in Set.Icc 0 t, M.btilde α ℓ B (t - u)
        ∂(SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) (M.Gtilde α)))
    (hdec2 : ∀ j : ℕ, ((M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map fun ω => (M.T j ω).toReal).withDensity
        (fun u => ENNReal.ofReal (Real.exp (α * u))) = QueueingFundamentals.MG1.convPow (M.Gtilde α) j)
    (hch : ∀ η : ℝ, 0 < η → η < 1 → ∃ δ > 0, ∀ (ℓ : ℕ) (t : ℝ), 0 ≤ t →
      (SmithRegenerative.Equilibrium.mean (M.Gtilde α)).toReal * ℓ ≤ (1 - η) * t →
        QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ (Set.Ioi ((1 - η / 2) * t)) ≤
          ENNReal.ofReal (Real.exp (-δ * t))) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ B : Set ((Fin (2 * k t + 1) → Path S) × ℝ), MeasurableSet B →
      |Real.exp (α * t) *
          (M.P {ω | k t < M.strad t ω ∧ (M.win (k t) t ω, M.age t ω) ∈ B ∧
            ENNReal.ofReal t < M.Γ ω}).toReal -
        M.rate α * ∫ u in Set.Ioi 0, M.btilde α (k t) B u| ≤ ε := by
  intro ε hε
  have hα : 0 ≤ α := h1.1
  obtain ⟨hA, hAw⟩ := h4
  have : IsProbabilityMeasure (M.Gtilde α) := ⟨Gtilde_univ M h1⟩
  have hprob : ∀ ℓ, QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ Set.univ = 1 := fun ℓ => by
    have := SmithRegenerative.Equilibrium.T2Glue.convPow_isProb (M.Gtilde α) ℓ
    exact measure_univ
  set U := SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) (M.Gtilde α) with hUdef
  have hUfin : ∀ x, U (Set.Icc 0 x) < ⊤ := fun x =>
    SmithRegenerative.Equilibrium.T2Glue.renewal_Icc_lt_top _ _ (by simp)
      (isCycleLaw_Gtilde M h0 h1) x
  haveI : SFinite U := by
    rw [hUdef, SmithRegenerative.Equilibrium.renewalMeasure]
    have : ∀ n, SFinite ((Measure.dirac (0:ℝ)).conv
        (QueueingFundamentals.MG1.convPow (M.Gtilde α) n)) := fun n => by
      have := SmithRegenerative.Equilibrium.T2Glue.convPow_isProb (M.Gtilde α) n
      infer_instance
    infer_instance
  have hLI : 0 < (M.lamInv α).toReal :=
    ENNReal.toReal_pos (lamInv_pos M h0 h1).ne' (show M.lamInv α < ⊤ from h3).ne
  set lam := M.rate α with hlamdef
  have hlam_pos : 0 < lam := inv_pos.2 hLI
  have hlam : 0 ≤ lam := hlam_pos.le
  have hmean : (SmithRegenerative.Equilibrium.mean (M.Gtilde α)).toReal = lam⁻¹ := by
    rw [mean_Gtilde M α, hlamdef, Model.rate, inv_inv]
  set ε' := ε / 4 with hε'def
  have hε' : 0 < ε' := div_pos hε (by norm_num)
  obtain ⟨N, hN⟩ := tail_small hA hAw.2.1 (ENNReal.ofReal (ε' / (lam + 1)))
    (ENNReal.ofReal_pos.2 (div_pos hε' (by linarith)))
  set Mc : ℝ := (N : ℝ) with hMc
  have hMc0 : 0 ≤ Mc := Nat.cast_nonneg N
  have hApos : ∀ r, 0 ≤ r → 0 ≤ hA r := fun r hr =>
    le_trans (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (hAw.2.2 r hr)
  have hind_nonneg : ∀ r, 0 ≤ (Set.Iio Mc).indicator (fun _ => Real.exp (α * Mc)) r :=
    fun r => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) r
  set htot : ℝ → ℝ := fun r => hA r + (Set.Iio Mc).indicator (fun _ => Real.exp (α * Mc)) r
    with hhtot
  have hle : ∀ r, 0 ≤ r → hA r ≤ htot r := fun r _ => le_add_of_nonneg_right (hind_nonneg r)
  have hpos : ∀ r, 0 ≤ r → 0 ≤ htot r := fun r hr => add_nonneg (hApos r hr) (hind_nonneg r)
  have hanti : AntitoneOn htot (Set.Ici 0) := by
    intro a ha b hb hab
    show hA b + _ ≤ hA a + _
    refine add_le_add (hAw.1 ha hb hab) ?_
    by_cases hbM : b < Mc
    · rw [Set.indicator_of_mem (show b ∈ Set.Iio Mc from hbM),
        Set.indicator_of_mem (show a ∈ Set.Iio Mc from lt_of_le_of_lt hab hbM)]
    · rw [Set.indicator_of_notMem (show b ∉ Set.Iio Mc from hbM)]; exact hind_nonneg a
  have hint : IntegrableOn htot (Set.Ici 0) := by
    have hfin : (volume.restrict (Set.Ici (0:ℝ))) (Set.Iio Mc) ≠ ⊤ := by
      rw [Measure.restrict_apply measurableSet_Iio]
      exact ((measure_mono (show Set.Iio Mc ∩ Set.Ici 0 ⊆ Set.Icc 0 Mc from
        fun x hx => ⟨hx.2, hx.1.le⟩)).trans_lt measure_Icc_lt_top).ne
    have hi : IntegrableOn (fun r => (Set.Iio Mc).indicator (fun _ => Real.exp (α * Mc)) r)
        (Set.Ici 0) :=
      (MeasureTheory.integrable_indicator_iff measurableSet_Iio).2 (integrableOn_const hfin)
    exact Integrable.add hAw.2.1 hi
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 (hUKR htot hanti hint ε' hε')
  have hukr : ∀ s, x0 ≤ s → ∀ b : ℝ → ℝ≥0∞, Measurable b →
      (∀ r, 0 ≤ r → b r ≤ ENNReal.ofReal (htot r)) →
      (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) ≤
          ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) + ENNReal.ofReal ε' ∧
        ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, b r) ≤
          (∫⁻ u in Set.Icc 0 s, b (s - u) ∂U) + ENNReal.ofReal ε' := by
    intro s hs b hb hbh
    refine ukr_lin U lam hlam htot hpos hanti hint hUfin ε' s ?_ b hb hbh
    intro b' hb' hb'h
    have := hx0 s hs b' hb' hb'h
    rwa [hmean, inv_inv] at this
  have hdom : ∀ r, 0 ≤ r → r < Mc →
      ENNReal.ofReal (Real.exp (α * r)) ≤ ENNReal.ofReal (htot r) := by
    intro r hr hrM
    refine ENNReal.ofReal_le_ofReal ?_
    show Real.exp (α * r) ≤ hA r + (Set.Iio Mc).indicator (fun _ => Real.exp (α * Mc)) r
    rw [Set.indicator_of_mem (show r ∈ Set.Iio Mc from hrM)]
    have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hrM.le hα)
    linarith [hApos r hr]
  have hI2 : ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, (Set.Ici Mc).indicator (hQ M α) r) ≤
      ENNReal.ofReal ε' := by
    calc ENNReal.ofReal lam * (∫⁻ r in Set.Ioi 0, (Set.Ici Mc).indicator (hQ M α) r)
        ≤ ENNReal.ofReal lam * ENNReal.ofReal (ε' / (lam + 1)) :=
          mul_le_mul' le_rfl ((I2_le M hAw Mc hMc0).trans hN.le)
      _ = ENNReal.ofReal (lam * (ε' / (lam + 1))) := (ENNReal.ofReal_mul hlam).symm
      _ ≤ ENNReal.ofReal ε' := ENNReal.ofReal_le_ofReal (by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]; nlinarith)
  obtain ⟨c, hc, hkt⟩ := hkg
  set c' := max c (lam / 2) with hc'
  have hc'lt : c' < lam := max_lt hc (by linarith)
  have hc'pos : 0 < c' := lt_of_lt_of_le (by linarith) (le_max_right c (lam / 2))
  set η := 1 - c' / lam with hη
  have hη0 : 0 < η := by rw [hη, sub_pos, div_lt_one hlam_pos]; exact hc'lt
  have hη1 : η < 1 := by rw [hη]; linarith [div_pos hc'pos hlam_pos]
  obtain ⟨δ, hδ, hchδ⟩ := hch η hη0 hη1
  have hKfin : ENNReal.ofReal (hA 0) * U (Set.Icc 0 x0) + ENNReal.ofReal (Real.exp (α * Mc)) *
      (U (Set.Icc 0 x0) + ENNReal.ofReal lam * ENNReal.ofReal Mc) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hUfin x0).ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨(hUfin x0).ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩)⟩
  set Kt := (ENNReal.ofReal (hA 0) * U (Set.Icc 0 x0) + ENNReal.ofReal (Real.exp (α * Mc)) *
      (U (Set.Icc 0 x0) + ENNReal.ofReal lam * ENNReal.ofReal Mc)).toReal with hKt
  have hKt0 : 0 ≤ Kt := ENNReal.toReal_nonneg
  have hexp : ∀ᶠ t in atTop, Real.exp (-δ * t) < ε' / (Kt + 1) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hδ)
    have := h.eventually (gt_mem_nhds (show (0:ℝ) < ε' / (Kt + 1) from div_pos hε' (by linarith)))
    refine this.mono fun t ht => ?_
    simpa [neg_mul] using ht
  filter_upwards [hkt, hexp, eventually_ge_atTop 0, eventually_ge_atTop x0,
    eventually_ge_atTop (2 * x0 / η)] with t hkt' hexp' ht0 htx0 htη
  intro B hB
  have hct : (ENNReal.ofReal (hA 0) * U (Set.Icc 0 x0) + ENNReal.ofReal (Real.exp (α * Mc)) *
      (U (Set.Icc 0 x0) + ENNReal.ofReal lam * ENNReal.ofReal Mc)) *
        QueueingFundamentals.MG1.convPow (M.Gtilde α) (k t) (Set.Ioi (t - x0)) ≤
          ENNReal.ofReal ε' := by
    have hm : (SmithRegenerative.Equilibrium.mean (M.Gtilde α)).toReal * (k t : ℝ) ≤
        (1 - η) * t := by
      rw [hmean, hη, sub_sub_cancel]
      have : (k t : ℝ) ≤ c' * t := hkt'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0)
      calc lam⁻¹ * (k t : ℝ) ≤ lam⁻¹ * (c' * t) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hlam)
        _ = c' / lam * t := by rw [div_eq_mul_inv]; ring
    have hsub : Set.Ioi (t - x0) ⊆ Set.Ioi ((1 - η / 2) * t) := Set.Ioi_subset_Ioi (by
      have : 2 * x0 ≤ t * η := (div_le_iff₀ hη0).1 htη
      nlinarith)
    calc _ ≤ ENNReal.ofReal Kt * ENNReal.ofReal (Real.exp (-δ * t)) := by
          rw [hKt, ENNReal.ofReal_toReal hKfin]
          exact mul_le_mul' le_rfl ((measure_mono hsub).trans (hchδ (k t) t ht0 hm))
      _ = ENNReal.ofReal (Kt * Real.exp (-δ * t)) := (ENNReal.ofReal_mul hKt0).symm
      _ ≤ ENNReal.ofReal ε' := ENNReal.ofReal_le_ofReal (by
          have h1' : Kt * Real.exp (-δ * t) ≤ Kt * (ε' / (Kt + 1)) :=
            mul_le_mul_of_nonneg_left hexp'.le hKt0
          have h2' : Kt * (ε' / (Kt + 1)) ≤ ε' := by
            rw [← mul_div_assoc, div_le_iff₀ (by linarith)]; nlinarith
          linarith)
  rw [hdec1 (k t) t ht0 B hB]
  have hab := assemble M hreg α hα (k t) B hB U lam ε' x0 t Mc htot hA hAw hle hukr hdom
    (hdec2 (k t)) (hprob (k t)) hI2 hct
  have hY := Y_lt_top M hreg α hα (k t) B hB (hdec2 (k t)) (hprob (k t)) hAw
  rw [int_Icc_eq M α (k t) B hB U t, int_Ioi_eq M α (k t) B hB]
  have h4e : ENNReal.ofReal ε' + ENNReal.ofReal ε' + ENNReal.ofReal ε' + ENNReal.ofReal ε' =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hε'.le hε'.le, ← ENNReal.ofReal_add (add_nonneg hε'.le hε'.le) hε'.le,
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg hε'.le hε'.le) hε'.le) hε'.le]
    congr 1; rw [hε'def]; ring
  rw [h4e] at hab
  exact abs_le_two _ _ lam ε hlam hε.le hY.ne hab.1 hab.2

end TabooRegen.UC

open TabooRegen TabooRegen.Model in
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h2 : M.A2) (h3 : M.A3 α) (h4 : M.A4 α) (h7 : M.A7)
    (k : ℝ → ℕ) (hk : MonotoneOn k (Set.Ici 0))
    (hkg : ∃ c < M.rate α, ∀ᶠ t in atTop, (k t : ℝ) ≤ c * t) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ B : Set ((Fin (2 * k t + 1) → Path S) × ℝ), MeasurableSet B →
      |Real.exp (α * t) *
          (M.P {ω | k t < M.strad t ω ∧ (M.win (k t) t ω, M.age t ω) ∈ B ∧
            ENNReal.ofReal t < M.Γ ω}).toReal -
        M.rate α * ∫ u in Set.Ioi 0, M.btilde α (k t) B u| ≤ ε := by
  have : IsProbabilityMeasure (M.Gtilde α) := ⟨TabooRegen.Prop2.Gtilde_univ M h1⟩
  have hF : M.Gtilde α (Set.Iio 0) = 0 := TabooRegen.Prop2.Gtilde_Iio M α
  have hm : SmithRegenerative.Equilibrium.mean (M.Gtilde α) < ⊤ := by
    rw [TabooRegen.Prop2.mean_Gtilde M α]; exact h3
  exact TabooRegen.UC.uc_core M hreg h0 h1 h3 h4 k hkg
    (fun h hh hhi => TabooRegen.uniform_key_renewal (M.Gtilde α) hF
      (TabooRegen.Prop2.inClassS_Gtilde M h2) hm h hh hhi)
    (fun l t ht B hB => (TabooRegen.renewal_decomposition_4_2 M hreg h0 h1 h2 h3 h4 h7 l t ht B hB).1)
    (fun j => (TabooRegen.renewal_decomposition_4_2 M hreg h0 h1 h2 h3 h4 h7 0 0 le_rfl ∅
      MeasurableSet.empty).2 j)
    (TabooRegen.chernoff_tail (M.Gtilde α) hF (TabooRegen.exp_moment_of_A7 M h1 h7)).2
