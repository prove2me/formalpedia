-- Prove2me | solution 1 for TabooRegen.integral_btilde
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T14:53:36.549337+00:00
-- url     : https://prove2.me/submissions/1a1f935d-43aa-4b94-b3ba-5834f0de0982

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace TabooRegen.IntB

open TabooRegen TabooRegen.Model

open KurtzProtter91.Integrals (IsCadlag)

lemma isCadlag_comp {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] (x : ℝ≥0 → E)
    (hx : IsCadlag x) (f : E → F) (hf : Continuous f) : IsCadlag (f ∘ x) := by
  refine ⟨fun t => (hf.continuousAt).comp_continuousWithinAt (hx.1 t), fun t ht => ?_⟩
  obtain ⟨a, ha⟩ := hx.2 t ht
  exact ⟨f a, (hf.tendsto a).comp ha⟩

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

/-- `Ψ = inf_j (T(j-1) + γ_j)`: the first exit read off the cycles -/
noncomputable def Ψ (ω : Ω) : ℝ≥0∞ := ⨅ j, (M.Tm j ω + M.γ j ω)

lemma Γ_le_Tm_add_γ (ω : Ω) (j : ℕ) : M.Γ ω ≤ M.Tm j ω + M.γ j ω := by
  unfold Model.γ exitTime
  rw [ENNReal.add_iInf]
  refine le_iInf fun s => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hs => ?_
  rw [M.W_eq] at hs
  unfold cycleOf at hs
  split_ifs at hs with hlt
  · obtain ⟨a, ha, hxa⟩ := hs
    have hfin : prevTime M.T j ω + (s : ℝ≥0∞) ≠ ⊤ := ne_top_of_lt hlt
    have hx : M.X ω (prevTime M.T j ω + (s : ℝ≥0∞)).toNNReal = a := Sum.inl_injective hxa
    unfold Model.Γ exitTime
    refine (iInf₂_le (prevTime M.T j ω + (s : ℝ≥0∞)).toNNReal ⟨a, ha, congrArg Sum.inl hx⟩).trans ?_
    rw [ENNReal.coe_toNNReal hfin]
    rfl
  · obtain ⟨a, _, hxa⟩ := hs
    exact absurd hxa (by simp)

lemma Γ_le_Ψ (ω : Ω) : M.Γ ω ≤ Ψ M ω := le_iInf fun j => Γ_le_Tm_add_γ M ω j

lemma Ψ_le_Γ (ω : Ω) (n : ℕ) (h : M.Γ ω < M.T n ω) : Ψ M ω ≤ M.Γ ω := by
  by_contra hlt
  push_neg at hlt
  have hb : M.Γ ω < min (Ψ M ω) (M.T n ω) := lt_min hlt h
  unfold Model.Γ exitTime at hb
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 hb
  obtain ⟨hex, ht⟩ := iInf_lt_iff.1 ht
  have htn : (t : ℝ≥0∞) < M.T n ω := lt_of_lt_of_le ht (min_le_right _ _)
  have hex' : ∃ m, (t : ℝ≥0∞) < M.T m ω := ⟨n, htn⟩
  classical
  set j := Nat.find hex' with hj
  have hjt : (t : ℝ≥0∞) < M.T j ω := Nat.find_spec hex'
  have hTm : M.Tm j ω ≤ t := by
    unfold Model.Tm prevTime
    split_ifs with h0
    · positivity
    · have := Nat.find_min hex' (show j - 1 < j by omega)
      exact not_lt.1 this
  have hTmfin : M.Tm j ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hTm
  set s' : ℝ≥0 := t - (M.Tm j ω).toNNReal with hs'
  have hsum : M.Tm j ω + (s' : ℝ≥0∞) = t := by
    rw [hs', ENNReal.coe_sub, ENNReal.coe_toNNReal hTmfin]
    exact add_tsub_cancel_of_le hTm
  have hγ : M.γ j ω ≤ s' := by
    unfold Model.γ exitTime
    refine iInf₂_le s' ?_
    rw [M.W_eq]
    unfold cycleOf
    have hc : prevTime M.T j ω + (s' : ℝ≥0∞) < M.T j ω := by
      change M.Tm j ω + (s' : ℝ≥0∞) < M.T j ω
      rw [hsum]; exact hjt
    rw [if_pos hc]
    obtain ⟨a, ha, hxa⟩ := hex
    refine ⟨a, ha, ?_⟩
    change Sum.inl (M.X ω (M.Tm j ω + (s' : ℝ≥0∞)).toNNReal) = Sum.inl a
    rw [hsum, ENNReal.toNNReal_coe]
    exact hxa
  have h1 : Ψ M ω ≤ M.Tm j ω + M.γ j ω := iInf_le _ j
  have h2 : M.Tm j ω + M.γ j ω ≤ t := by
    calc M.Tm j ω + M.γ j ω ≤ M.Tm j ω + s' := add_le_add_right hγ _
      _ = t := hsum
  have h3 : (t : ℝ≥0∞) < Ψ M ω := lt_of_lt_of_le ht (min_le_left _ _)
  exact absurd (h1.trans h2) (not_le.2 h3)

lemma lt_Γ_iff_lt_Ψ (ω : Ω) (n : ℕ) (x : ℝ≥0∞) (hx : x < M.T n ω) :
    x < M.Γ ω ↔ x < Ψ M ω := by
  constructor
  · intro h; exact lt_of_lt_of_le h (Γ_le_Ψ M ω)
  · intro h
    by_contra hΓ
    push_neg at hΓ
    exact absurd (lt_of_lt_of_le h ((Ψ_le_Γ M ω n (lt_of_le_of_lt hΓ hx)).trans hΓ)) (lt_irrefl _)

/-- the exit decomposition inside the cycle `ℓ + 1` -/
lemma lt_Γ_iff (ℓ : ℕ) (ω : Ω) (x : ℝ≥0∞) (hx : M.T ℓ ω + x < M.T (ℓ + 1) ω) :
    M.T ℓ ω + x < M.Γ ω ↔ M.T ℓ ω ≤ M.Γ ω ∧ x < M.γ (ℓ + 1) ω := by
  have hTm : M.Tm (ℓ + 1) ω = M.T ℓ ω := by simp [Model.Tm, prevTime]
  have hfin : M.T ℓ ω ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt le_self_add hx)
  constructor
  · intro h
    refine ⟨le_self_add.trans h.le, ?_⟩
    have h2 := lt_of_lt_of_le h (Γ_le_Tm_add_γ M ω (ℓ + 1))
    rw [hTm] at h2
    exact (ENNReal.add_lt_add_iff_left hfin).1 h2
  · rintro ⟨hle, hγ⟩
    rw [lt_Γ_iff_lt_Ψ M ω (ℓ + 1) _ hx]
    have hm : M.T ℓ ω + x < min (M.T ℓ ω + M.γ (ℓ + 1) ω) (M.T (ℓ + 1) ω) :=
      lt_min ((ENNReal.add_lt_add_iff_left hfin).2 hγ) hx
    refine lt_of_lt_of_le hm (le_iInf fun j => ?_)
    rcases lt_trichotomy j (ℓ + 1) with hj | hj | hj
    · rw [γ_top_of_le M hle (show j ≤ ℓ by omega), add_top]; exact le_top
    · subst hj; rw [hTm]; exact min_le_left _ _
    · refine (min_le_right _ _).trans (le_trans ?_ le_self_add)
      have : M.Tm j ω = M.T (j - 1) ω := by
        simp [Model.Tm, prevTime, show j ≠ 0 by omega]
      rw [this]; exact T_mono' M (by omega)

lemma Q_eq_P (h0 : ∀ ω, M.T 0 ω = 0) : M.Q = M.P := by
  have := M.isProb
  have hE : {ω | M.T 0 ω ≤ M.Γ ω} = Set.univ := by ext ω; simp [h0]
  unfold Model.Q
  rw [hE, ProbabilityTheory.cond_univ]

/-- the joint event of `b̃` in `(u, ω)` -/
def Eset (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) : Set (ℝ × Ω) :=
  {p | ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) p.2), p.1 - (M.T ℓ p.2).toReal) ∈ B ∧
      M.T ℓ p.2 ≤ ENNReal.ofReal p.1 ∧ ENNReal.ofReal p.1 < M.T (ℓ + 1) p.2 ∧
      ENNReal.ofReal p.1 < M.Γ p.2}

lemma measurableSet_Eset (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) : MeasurableSet (Eset M ℓ B) := by
  have h1 : Measurable fun p : ℝ × Ω =>
      ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) p.2), p.1 - (M.T ℓ p.2).toReal) :=
    (measurable_pi_lambda _ fun i => (M.measurable_W _).comp measurable_snd).prodMk
      (measurable_fst.sub ((M.measurable_T ℓ).ennreal_toReal.comp measurable_snd))
  exact (hB.preimage h1).inter ((measurableSet_le ((M.measurable_T ℓ).comp measurable_snd)
      (ENNReal.measurable_ofReal.comp measurable_fst)).inter
      ((measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((M.measurable_T (ℓ + 1)).comp measurable_snd)).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((measurable_Γ M).comp measurable_snd))))

/-- the joint integrand -/
noncomputable def g (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (p : ℝ × Ω) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (α * p.1)) * (Eset M ℓ B).indicator (fun _ => (1 : ℝ≥0∞)) p

lemma measurable_g (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) : Measurable (g M α ℓ B) :=
  (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul measurable_fst))).mul
    (measurable_const.indicator (measurableSet_Eset M ℓ B hB))

lemma ofReal_btilde (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) (u : ℝ) :
    ENNReal.ofReal (M.btilde α ℓ B u) = ∫⁻ ω, g M α ℓ B (u, ω) ∂M.P := by
  haveI : IsProbabilityMeasure M.P := M.isProb
  show _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (α * u)) *
    (Eset M ℓ B).indicator (fun _ => (1 : ℝ≥0∞)) (u, ω) ∂M.P
  have hm : Measurable fun ω => (Eset M ℓ B).indicator (fun _ => (1 : ℝ≥0∞)) (u, ω) :=
    (measurable_const.indicator (measurableSet_Eset M ℓ B hB)).comp measurable_prodMk_left
  rw [lintegral_const_mul _ hm]
  have hs : MeasurableSet (Prod.mk u ⁻¹' Eset M ℓ B) :=
    measurable_prodMk_left (measurableSet_Eset M ℓ B hB)
  have hind : (fun ω => (Eset M ℓ B).indicator (fun _ => (1 : ℝ≥0∞)) (u, ω)) =
      (Prod.mk u ⁻¹' Eset M ℓ B).indicator 1 := by
    ext ω; rfl
  rw [hind, lintegral_indicator_one hs]
  unfold Model.btilde
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rfl

/-- the inner `x`-integrand of `PstarNum` -/
noncomputable def hx (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (ω : Ω) (x : ℝ) :
    ℝ≥0∞ :=
  {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω)}.indicator
    (fun x => ENNReal.ofReal (Real.exp (α * x)) *
      B.indicator (fun _ => (1 : ℝ≥0∞)) ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), x)) x

lemma inner_eq (α : ℝ) (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ))
    (hB : MeasurableSet B) (ω : Ω) :
    ∫⁻ u in Set.Ioi 0, g M α ℓ B (u, ω) =
      {ω | M.T ℓ ω ≤ M.Γ ω}.indicator (fun ω => ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
        ∫⁻ x in {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω)},
          ENNReal.ofReal (Real.exp (α * x)) *
            B.indicator (fun _ => (1 : ℝ≥0∞)) ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), x)) ω := by
  classical
  set G : Set Ω := {ω | M.T ℓ ω ≤ M.Γ ω} with hGdef
  by_cases hTf : M.T ℓ ω = ⊤
  · have hnG : ω ∉ G := by
      intro hG
      have h1 : M.Γ ω = ⊤ := top_le_iff.1 (hTf ▸ hG)
      exact (M.T_top ℓ ω hTf).ne h1
    have hz : ∀ u, g M α ℓ B (u, ω) = 0 := by
      intro u
      have : (u, ω) ∉ Eset M ℓ B := by
        rintro ⟨_, h1, _⟩
        rw [hTf] at h1
        exact ENNReal.ofReal_ne_top (top_le_iff.1 h1)
      simp [g, this]
    simp [hz, hnG]
  set c : ℝ := (M.T ℓ ω).toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hcT : M.T ℓ ω = ENNReal.ofReal c := (ENNReal.ofReal_toReal hTf).symm
  set K : ℝ≥0∞ := G.indicator (fun _ => ENNReal.ofReal (Real.exp (α * c))) ω with hK
  have hτ : M.τ (ℓ + 1) ω = M.T (ℓ + 1) ω - M.T ℓ ω := by
    simp [Model.τ, Model.Tm, prevTime]
  have hiff : ∀ u : ℝ, 0 ≤ u → ((u, ω) ∈ Eset M ℓ B ↔ (ω ∈ G ∧ (0 ≤ u - c ∧
      ENNReal.ofReal (u - c) < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω)) ∧
      ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), u - c) ∈ B)) := by
    intro u hu
    have hsplit : 0 ≤ u - c → ENNReal.ofReal u = M.T ℓ ω + ENNReal.ofReal (u - c) := by
      intro hx
      rw [hcT, ← ENNReal.ofReal_add hc0 hx]; congr 1; ring
    have hlt : ∀ y : ℝ≥0∞, y < M.τ (ℓ + 1) ω ↔ M.T ℓ ω + y < M.T (ℓ + 1) ω := by
      intro y; rw [hτ]; exact (ENNReal.cancel_of_ne hTf).lt_tsub_iff_left
    constructor
    · rintro ⟨hBm, hT1, hT2, hΓ⟩
      have hx : 0 ≤ u - c := by
        rw [hcT, ENNReal.ofReal_le_ofReal_iff hu] at hT1; linarith
      rw [hsplit hx] at hT2 hΓ
      obtain ⟨hG, hγ⟩ := (lt_Γ_iff M ℓ ω _ hT2).1 hΓ
      exact ⟨hG, ⟨hx, lt_min hγ ((hlt _).2 hT2)⟩, hBm⟩
    · rintro ⟨hG, ⟨hx, hmin⟩, hBm⟩
      have hT2 : M.T ℓ ω + ENNReal.ofReal (u - c) < M.T (ℓ + 1) ω :=
        (hlt _).1 (lt_of_lt_of_le hmin (min_le_right _ _))
      refine ⟨hBm, ?_, ?_, ?_⟩
      · rw [hsplit hx]; exact le_self_add
      · rw [hsplit hx]; exact hT2
      · rw [hsplit hx]
        exact (lt_Γ_iff M ℓ ω _ hT2).2 ⟨hG, lt_of_lt_of_le hmin (min_le_left _ _)⟩
  have hpt : ∀ u : ℝ, 0 ≤ u → g M α ℓ B (u, ω) = K * hx M α ℓ B ω (u + -c) := by
    intro u hu
    have hexp : ENNReal.ofReal (Real.exp (α * u)) =
        ENNReal.ofReal (Real.exp (α * c)) * ENNReal.ofReal (Real.exp (α * (u + -c))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
    have hiff' := hiff u hu
    rw [show u - c = u + -c by ring] at hiff'
    unfold g hx
    rw [hK]
    by_cases hE : (u, ω) ∈ Eset M ℓ B
    · obtain ⟨hG, hS, hBm⟩ := hiff'.1 hE
      have hS' : u + -c ∈ {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω)} := hS
      rw [Set.indicator_of_mem hE, Set.indicator_of_mem hG, Set.indicator_of_mem hS',
        Set.indicator_of_mem hBm, hexp]
      ring
    · rw [Set.indicator_of_notMem hE, mul_zero]
      by_cases hG : ω ∈ G
      · by_cases hS : (0 ≤ u + -c ∧ ENNReal.ofReal (u + -c) < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω))
        · have hBm : ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), u + -c) ∉ B :=
            fun h => hE (hiff'.2 ⟨hG, hS, h⟩)
          have hS' : u + -c ∈ {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω)} := hS
          rw [Set.indicator_of_mem hS', Set.indicator_of_notMem hBm]; simp
        · have hS' : u + -c ∉ {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω)} := hS
          rw [Set.indicator_of_notMem hS']; simp
      · rw [Set.indicator_of_notMem hG]; simp
  have hmeasS : MeasurableSet {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω)} :=
    measurableSet_Ici.inter (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  calc ∫⁻ u in Set.Ioi 0, g M α ℓ B (u, ω)
      = ∫⁻ u in Set.Ici 0, g M α ℓ B (u, ω) := setLIntegral_congr Ioi_ae_eq_Ici
    _ = ∫⁻ u in Set.Ici 0, K * hx M α ℓ B ω (u + -c) :=
        setLIntegral_congr_fun measurableSet_Ici (fun u hu => hpt u hu)
    _ = ∫⁻ u, K * hx M α ℓ B ω (u + -c) := by
        refine setLIntegral_eq_of_support_subset fun u hu => ?_
        by_contra hneg
        simp only [Set.mem_Ici, not_le] at hneg
        apply hu
        have : u + -c ∉ {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω)} := by
          rintro ⟨h, _⟩; linarith
        simp only [hx]
        rw [Set.indicator_of_notMem this, mul_zero]
    _ = K * ∫⁻ u, hx M α ℓ B ω (u + -c) := by
        refine lintegral_const_mul K ?_
        refine Measurable.comp ?_ (measurable_add_const _)
        refine Measurable.indicator ?_ hmeasS
        refine (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (measurable_const.mul measurable_id))).mul ?_
        exact (measurable_const.indicator hB).comp (measurable_const.prodMk measurable_id)
    _ = K * ∫⁻ x, hx M α ℓ B ω x := by rw [lintegral_add_right_eq_self]
    _ = _ := by
        unfold hx
        rw [lintegral_indicator hmeasS, hK]
        by_cases hG : ω ∈ G
        · rw [Set.indicator_of_mem hG, Set.indicator_of_mem hG]
        · rw [Set.indicator_of_notMem hG, Set.indicator_of_notMem hG, zero_mul]

end TabooRegen.IntB

open MeasureTheory TabooRegen in
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h2 : M.A2) (h3 : M.A3 α) (h4 : M.A4 α) (h7 : M.A7) (ℓ : ℕ)
    (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (hB : MeasurableSet B) :
    ∫⁻ u in Set.Ioi 0, ENNReal.ofReal (M.btilde α ℓ B u) = M.PstarNum α ℓ B := by
  have : IsProbabilityMeasure M.P := M.isProb
  have hGm : MeasurableSet {ω | M.T ℓ ω ≤ M.Γ ω} :=
    measurableSet_le (M.measurable_T ℓ) (IntB.measurable_Γ M)
  calc ∫⁻ u in Set.Ioi 0, ENNReal.ofReal (M.btilde α ℓ B u)
      = ∫⁻ u in Set.Ioi 0, ∫⁻ ω, IntB.g M α ℓ B (u, ω) ∂M.P :=
        lintegral_congr fun u => IntB.ofReal_btilde M α ℓ B hB u
    _ = ∫⁻ ω, (∫⁻ u in Set.Ioi 0, IntB.g M α ℓ B (u, ω)) ∂M.P :=
        lintegral_lintegral_swap (f := fun u ω => IntB.g M α ℓ B (u, ω))
          (IntB.measurable_g M α ℓ B hB).aemeasurable
    _ = ∫⁻ ω, {ω | M.T ℓ ω ≤ M.Γ ω}.indicator (fun ω =>
          ENNReal.ofReal (Real.exp (α * (M.T ℓ ω).toReal)) *
          ∫⁻ x in {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < min (M.γ (ℓ + 1) ω) (M.τ (ℓ + 1) ω)},
            ENNReal.ofReal (Real.exp (α * x)) *
              B.indicator (fun _ => (1 : ℝ≥0∞)) ((fun i : Fin (2 * ℓ + 1) => M.W (1 + i) ω), x))
          ω ∂M.P :=
        lintegral_congr fun ω => IntB.inner_eq M α ℓ B hB ω
    _ = M.PstarNum α ℓ B := by
        rw [lintegral_indicator hGm]
        unfold Model.PstarNum
        rw [IntB.Q_eq_P M h0]
        simp [h0]
