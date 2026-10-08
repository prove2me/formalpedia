-- Prove2me | solution 1 for TeschlODE.Planar.unique_connecting_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-06T20:14:34.894985+00:00
-- url     : https://prove2.me/submissions/2113447e-960c-49c7-ada7-87790cf22d79

import Mathlib
import Definitions.Def_TeschlODE_Planar_flow
import Definitions.Def_TeschlODE_Planar_orbit
import Definitions.Def_TeschlODE_Planar_halfOrbit
import Definitions.Def_TeschlODE_Planar_omegaLimitSet
import Definitions.Def_TeschlODE_Planar_IsPeriodicPoint
import Definitions.Def_TeschlODE_Planar_IsTransversalArc
import Theorems.Thm_JordanCurve_jordan_curve_theorem
import Theorems.Thm_TeschlODE_Planar_omegaLimitSet_inter_arc_subsingleton
import Theorems.Thm_TeschlODE_Planar_periodic_of_omegaLimitSet_inter_halfOrbit


/-! Flow foundations for `TeschlODE.Planar.flow`: uniqueness of integral curves, the maximal
integral curve, the group law, time reversal, and the local flow. -/

open Set Filter Topology Metric
open scoped NNReal

namespace PBF

open TeschlODE.Planar

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {M : Set (Fin n → ℝ)}

/-- `φ` is an integral curve of `f` in `M` on `J`. -/
def IsSol (f : (Fin n → ℝ) → Fin n → ℝ) (M : Set (Fin n → ℝ)) (J : Set ℝ)
    (φ : ℝ → Fin n → ℝ) : Prop :=
  ∀ s ∈ J, φ s ∈ M ∧ HasDerivAt φ (f (φ s)) s

lemma IsSol.mono {J J' : Set ℝ} {φ : ℝ → Fin n → ℝ} (h : IsSol f M J φ) (hJ : J' ⊆ J) :
    IsSol f M J' φ := fun s hs => h s (hJ hs)

lemma IsSol.continuousOn {J : Set ℝ} {φ : ℝ → Fin n → ℝ} (h : IsSol f M J φ) :
    ContinuousOn φ J := fun s hs => (h s hs).2.continuousAt.continuousWithinAt

lemma locLip (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) : LocallyLipschitzOn M f := by
  intro x hx
  obtain ⟨K, t, ht, hl⟩ := (hf.contDiffAt (hM.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hl⟩

lemma eqOn_Icc_right (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {φ ψ : ℝ → Fin n → ℝ}
    {a b : ℝ} (hφ : IsSol f M (Icc a b) φ) (hψ : IsSol f M (Icc a b) ψ) (h : φ a = ψ a) :
    EqOn φ ψ (Icc a b) := by
  set K := φ '' Icc a b ∪ ψ '' Icc a b
  have hK : IsCompact K :=
    (isCompact_Icc.image_of_continuousOn hφ.continuousOn).union
      (isCompact_Icc.image_of_continuousOn hψ.continuousOn)
  have hKM : K ⊆ M := by
    rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact (hφ s hs).1
    · exact (hψ s hs).1
  obtain ⟨L, hL⟩ := ((locLip hM hf).mono hKM).exists_lipschitzOnWith_of_compact hK
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => f) (s := fun _ => K)
    (fun _ _ => hL) hφ.continuousOn
    (fun t ht => (hφ t (Ico_subset_Icc_self ht)).2.hasDerivWithinAt)
    (fun t ht => Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩) hψ.continuousOn
    (fun t ht => (hψ t (Ico_subset_Icc_self ht)).2.hasDerivWithinAt)
    (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) h

lemma eqOn_Icc_left (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {φ ψ : ℝ → Fin n → ℝ}
    {a b : ℝ} (hφ : IsSol f M (Icc a b) φ) (hψ : IsSol f M (Icc a b) ψ) (h : φ b = ψ b) :
    EqOn φ ψ (Icc a b) := by
  set K := φ '' Icc a b ∪ ψ '' Icc a b
  have hK : IsCompact K :=
    (isCompact_Icc.image_of_continuousOn hφ.continuousOn).union
      (isCompact_Icc.image_of_continuousOn hψ.continuousOn)
  have hKM : K ⊆ M := by
    rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact (hφ s hs).1
    · exact (hψ s hs).1
  obtain ⟨L, hL⟩ := ((locLip hM hf).mono hKM).exists_lipschitzOnWith_of_compact hK
  exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => f) (s := fun _ => K)
    (fun _ _ => hL) hφ.continuousOn
    (fun t ht => (hφ t (Ioc_subset_Icc_self ht)).2.hasDerivWithinAt)
    (fun t ht => Or.inl ⟨t, Ioc_subset_Icc_self ht, rfl⟩) hψ.continuousOn
    (fun t ht => (hψ t (Ioc_subset_Icc_self ht)).2.hasDerivWithinAt)
    (fun t ht => Or.inr ⟨t, Ioc_subset_Icc_self ht, rfl⟩) h

/-- Uniqueness of integral curves on intervals. -/
lemma eqOn_of_sol (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J₁ J₂ : Set ℝ}
    (h₁ : J₁.OrdConnected) (h₂ : J₂.OrdConnected) {φ ψ : ℝ → Fin n → ℝ}
    (hφ : IsSol f M J₁ φ) (hψ : IsSol f M J₂ ψ) {t₀ : ℝ} (ht₁ : t₀ ∈ J₁) (ht₂ : t₀ ∈ J₂)
    (h : φ t₀ = ψ t₀) : EqOn φ ψ (J₁ ∩ J₂) := by
  intro t ⟨htJ₁, htJ₂⟩
  rcases le_total t₀ t with hle | hle
  · have hsub : Icc t₀ t ⊆ J₁ ∩ J₂ := subset_inter (h₁.out ht₁ htJ₁) (h₂.out ht₂ htJ₂)
    exact eqOn_Icc_right hM hf (hφ.mono (hsub.trans inter_subset_left))
      (hψ.mono (hsub.trans inter_subset_right)) h ⟨hle, le_rfl⟩
  · have hsub : Icc t t₀ ⊆ J₁ ∩ J₂ := subset_inter (h₁.out htJ₁ ht₁) (h₂.out htJ₂ ht₂)
    exact eqOn_Icc_left hM hf (hφ.mono (hsub.trans inter_subset_left))
      (hψ.mono (hsub.trans inter_subset_right)) h ⟨le_rfl, hle⟩

lemma mem_lifetime_iff {x : Fin n → ℝ} {t : ℝ} :
    t ∈ lifetime f M x ↔ ∃ (J : Set ℝ) (φ : ℝ → Fin n → ℝ), IsOpen J ∧ J.OrdConnected ∧
      (0 : ℝ) ∈ J ∧ t ∈ J ∧ φ 0 = x ∧ IsSol f M J φ := Iff.rfl

/-- The flow is the value of any integral curve through `x`. -/
lemma flow_eq_of_sol (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {t : ℝ}
    {J : Set ℝ} {φ : ℝ → Fin n → ℝ} (hJ : IsOpen J) (hJc : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    (ht : t ∈ J) (hφ0 : φ 0 = x) (hφ : IsSol f M J φ) : flow f M t x = φ t := by
  have hmem : t ∈ lifetime f M x := ⟨J, φ, hJ, hJc, h0, ht, hφ0, hφ⟩
  unfold flow
  rw [dif_pos hmem]
  obtain ⟨_, hJc', h0', ht', hφ0', hφ'⟩ := Classical.choose_spec (Classical.choose_spec hmem)
  exact eqOn_of_sol hM hf hJc' hJc hφ' hφ h0' h0 (hφ0'.trans hφ0.symm) ⟨ht', ht⟩

lemma isOpen_lifetime (x : Fin n → ℝ) : IsOpen (lifetime f M x) := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨J, φ, hJ, hJc, h0, ht, hφ0, hφ⟩
  exact Filter.mem_of_superset (hJ.mem_nhds ht) fun s hs => ⟨J, φ, hJ, hJc, h0, hs, hφ0, hφ⟩

lemma zero_mem_lifetime_of_mem {x : Fin n → ℝ} {t : ℝ} (ht : t ∈ lifetime f M x) :
    (0 : ℝ) ∈ lifetime f M x := by
  obtain ⟨J, φ, hJ, hJc, h0, -, hφ0, hφ⟩ := ht
  exact ⟨J, φ, hJ, hJc, h0, h0, hφ0, hφ⟩

lemma ordConnected_lifetime (x : Fin n → ℝ) : (lifetime f M x).OrdConnected := by
  refine ⟨fun a ha b hb s hs => ?_⟩
  rcases le_total 0 s with h | h
  · obtain ⟨J, φ, hJ, hJc, h0, hb', hφ0, hφ⟩ := hb
    exact ⟨J, φ, hJ, hJc, h0, hJc.out h0 hb' ⟨h, hs.2⟩, hφ0, hφ⟩
  · obtain ⟨J, φ, hJ, hJc, h0, ha', hφ0, hφ⟩ := ha
    exact ⟨J, φ, hJ, hJc, h0, hJc.out ha' h0 ⟨hs.1, h⟩, hφ0, hφ⟩

/-- `t ↦ Φ(t, x)` is an integral curve on the whole lifetime. -/
lemma flow_sol (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (x : Fin n → ℝ) :
    IsSol f M (lifetime f M x) (fun t => flow f M t x) := by
  intro t ht
  obtain ⟨J, φ, hJ, hJc, h0, htJ, hφ0, hφ⟩ := ht
  have heq : (fun s => flow f M s x) =ᶠ[𝓝 t] φ :=
    Filter.mem_of_superset (hJ.mem_nhds htJ) fun s hs =>
      flow_eq_of_sol hM hf hJ hJc h0 hs hφ0 hφ
  have hft : flow f M t x = φ t := heq.eq_of_nhds
  show flow f M t x ∈ M ∧ HasDerivAt (fun t => flow f M t x) (f (flow f M t x)) t
  rw [hft]
  exact ⟨(hφ t htJ).1, (hφ t htJ).2.congr_of_eventuallyEq heq⟩

lemma flow_zero (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (h : (0 : ℝ) ∈ lifetime f M x) : flow f M 0 x = x := by
  obtain ⟨J, φ, hJ, hJc, h0, -, hφ0, hφ⟩ := h
  rw [flow_eq_of_sol hM hf hJ hJc h0 h0 hφ0 hφ, hφ0]

lemma flow_mem (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {t : ℝ}
    (ht : t ∈ lifetime f M x) : flow f M t x ∈ M :=
  (flow_sol hM hf x t ht).1

lemma mem_of_mem_lifetime {x : Fin n → ℝ} {t : ℝ} (ht : t ∈ lifetime f M x) : x ∈ M := by
  obtain ⟨J, φ, hJ, hJc, h0, -, hφ0, hφ⟩ := ht
  rw [← hφ0]
  exact (hφ 0 h0).1

lemma ordConnected_union_of_mem {A B : Set ℝ} (hA : A.OrdConnected) (hB : B.OrdConnected)
    {a : ℝ} (haA : a ∈ A) (haB : a ∈ B) : (A ∪ B).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  rcases le_total z a with h | h
  · rcases hx with hx | hx
    · exact Or.inl (hA.out hx haA ⟨hz.1, h⟩)
    · exact Or.inr (hB.out hx haB ⟨hz.1, h⟩)
  · rcases hy with hy | hy
    · exact Or.inl (hA.out haA hy ⟨h, hz.2⟩)
    · exact Or.inr (hB.out haB hy ⟨h, hz.2⟩)

/-- Group law, lifetime part: `t ∈ I_{Φ(s,x)} ↔ t + s ∈ I_x`. -/
lemma mem_lifetime_flow (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {s t : ℝ}
    (hs : s ∈ lifetime f M x) : t ∈ lifetime f M (flow f M s x) ↔ t + s ∈ lifetime f M x := by
  set L := lifetime f M x
  have hφ := flow_sol hM hf x
  have hLo : IsOpen L := isOpen_lifetime x
  have hLc : L.OrdConnected := ordConnected_lifetime x
  constructor
  · classical
    rintro ⟨J, χ, hJ, hJc, h0, htJ, hχ0, hχ⟩
    -- glue `Φ(·, x)` on `L` with `χ(· - s)` on `J + s`
    set J' := {r : ℝ | r - s ∈ J}
    have hJ'o : IsOpen J' := hJ.preimage (continuous_id.sub continuous_const)
    have hJ'c : J'.OrdConnected := ⟨fun a ha b hb r hr => hJc.out ha hb
      ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩
    have hsJ' : s ∈ J' := by simp [J', h0]
    have hshift : IsSol f M J' (fun r => χ (r - s)) := by
      intro r hr
      refine ⟨(hχ _ hr).1, ?_⟩
      exact (hχ _ hr).2.comp_sub_const r s
    have hover : EqOn (fun r => flow f M r x) (fun r => χ (r - s)) (L ∩ J') :=
      eqOn_of_sol hM hf hLc hJ'c hφ hshift hs hsJ' (by simp [hχ0])
    let g : ℝ → Fin n → ℝ := fun r => if r ∈ L then flow f M r x else χ (r - s)
    have hgL : ∀ r ∈ L, g r = flow f M r x := fun r hr => if_pos hr
    have hgJ : ∀ r ∈ J', g r = χ (r - s) := by
      intro r hr
      by_cases hrL : r ∈ L
      · rw [hgL r hrL]; exact hover ⟨hrL, hr⟩
      · exact if_neg hrL
    have hg : IsSol f M (L ∪ J') g := by
      intro r hr
      rcases hr with hr | hr
      · have heq : g =ᶠ[𝓝 r] fun r => flow f M r x :=
          Filter.mem_of_superset (hLo.mem_nhds hr) fun r' hr' => hgL r' hr'
        rw [heq.eq_of_nhds]
        exact ⟨(hφ r hr).1, (hφ r hr).2.congr_of_eventuallyEq heq⟩
      · have heq : g =ᶠ[𝓝 r] fun r => χ (r - s) :=
          Filter.mem_of_superset (hJ'o.mem_nhds hr) fun r' hr' => hgJ r' hr'
        rw [heq.eq_of_nhds]
        exact ⟨(hshift r hr).1, (hshift r hr).2.congr_of_eventuallyEq heq⟩
    have h0L : (0 : ℝ) ∈ L := zero_mem_lifetime_of_mem hs
    refine ⟨L ∪ J', g, hLo.union hJ'o, ordConnected_union_of_mem hLc hJ'c hs hsJ',
      Or.inl h0L, Or.inr (by simpa [J'] using htJ), ?_, hg⟩
    rw [hgL 0 h0L, flow_zero hM hf h0L]
  · intro hts
    set J' := {r : ℝ | r + s ∈ L}
    have hJ'o : IsOpen J' := hLo.preimage (continuous_id.add continuous_const)
    have hJ'c : J'.OrdConnected := ⟨fun a ha b hb r hr => hLc.out ha hb
      ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩
    refine ⟨J', fun r => flow f M (r + s) x, hJ'o, hJ'c, by simpa [J'] using hs, hts,
      by simp, fun r hr => ⟨(hφ _ hr).1, ?_⟩⟩
    exact (hφ _ hr).2.comp_add_const r s

/-- Group law: `Φ(t, Φ(s, x)) = Φ(t + s, x)`. -/
lemma flow_flow (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {s t : ℝ}
    (hs : s ∈ lifetime f M x) (hts : t + s ∈ lifetime f M x) :
    flow f M t (flow f M s x) = flow f M (t + s) x := by
  set L := lifetime f M x
  have hφ := flow_sol hM hf x
  set J' := {r : ℝ | r + s ∈ L}
  have hJ'o : IsOpen J' := (isOpen_lifetime x).preimage (continuous_id.add continuous_const)
  have hJ'c : J'.OrdConnected := ⟨fun a ha b hb r hr => (ordConnected_lifetime x).out ha hb
    ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩
  exact flow_eq_of_sol hM hf hJ'o hJ'c (by simpa [J'] using hs) hts (by simp)
    (fun r hr => ⟨(hφ _ hr).1, (hφ _ hr).2.comp_add_const r s⟩)

/-! ### Time reversal -/

lemma isSol_neg {J : Set ℝ} {φ : ℝ → Fin n → ℝ} (h : IsSol f M J φ) :
    IsSol (fun y => -f y) M {s | -s ∈ J} (fun s => φ (-s)) := by
  intro s hs
  refine ⟨(h _ hs).1, ?_⟩
  have h1 := (h _ hs).2
  have h2 : HasDerivAt (fun s : ℝ => -s) (-1) s := hasDerivAt_neg s
  have := h1.scomp s h2
  simpa [Function.comp_def] using this

lemma mem_lifetime_neg {x : Fin n → ℝ} {t : ℝ} :
    t ∈ lifetime (fun y => -f y) M x ↔ -t ∈ lifetime f M x := by
  constructor
  · rintro ⟨J, φ, hJ, hJc, h0, ht, hφ0, hφ⟩
    have := isSol_neg (f := fun y => -f y) (M := M) hφ
    simp only [neg_neg] at this
    refine ⟨{s | -s ∈ J}, fun s => φ (-s), hJ.preimage continuous_neg,
      ⟨fun a ha b hb r hr => hJc.out hb ha ⟨by linarith [hr.2], by linarith [hr.1]⟩⟩,
      by simpa using h0, by simpa using ht, by simpa using hφ0, ?_⟩
    intro s hs
    have h' := this s hs
    simpa using h'
  · rintro ⟨J, φ, hJ, hJc, h0, ht, hφ0, hφ⟩
    exact ⟨{s | -s ∈ J}, fun s => φ (-s), hJ.preimage continuous_neg,
      ⟨fun a ha b hb r hr => hJc.out hb ha ⟨by linarith [hr.2], by linarith [hr.1]⟩⟩,
      by simpa using h0, by simpa using ht, by simpa using hφ0, isSol_neg hφ⟩

lemma flow_neg (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {t : ℝ}
    (ht : -t ∈ lifetime f M x) : flow (fun y => -f y) M t x = flow f M (-t) x := by
  set L := lifetime f M x
  have hφ := isSol_neg (flow_sol hM hf x)
  exact flow_eq_of_sol hM hf.neg ((isOpen_lifetime x).preimage continuous_neg)
    ⟨fun a ha b hb r hr => (ordConnected_lifetime x).out hb ha
      ⟨by linarith [hr.2], by linarith [hr.1]⟩⟩
    (by simpa using zero_mem_lifetime_of_mem ht) ht
    (by simpa using flow_zero hM hf (zero_mem_lifetime_of_mem ht)) hφ

end PBF


/-! The local flow: uniform local existence near a point of `M`, staying in `M`, and Lipschitz in
the initial point. -/

open Set Filter Topology Metric Function
open scoped NNReal

namespace PBF

open TeschlODE.Planar

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {M : Set (Fin n → ℝ)}

/-- Picard–Lindelöf data around `x₀ ∈ M` with all values inside `M`. -/
lemma exists_picard (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ M) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0), 0 < (r : ℝ) ∧ closedBall x₀ (a : ℝ) ⊆ M ∧
      IsPicardLindelof (fun _ => f) (tmin := -ε) (tmax := ε) ⟨0, by constructor <;> linarith⟩
        x₀ a r L K := by
  have hfx : ContDiffAt ℝ 1 f x₀ := hf.contDiffAt (hM.mem_nhds hx₀)
  obtain ⟨K, s, hs, hl⟩ := hfx.exists_lipschitzOnWith
  obtain ⟨a, ha, has⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hs (hM.mem_nhds hx₀))
  set L : ℝ := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hball : closedBall x₀ (a / 2) ⊆ s ∩ M :=
    (closedBall_subset_ball (half_lt_self ha)).trans has
  have hb (x : Fin n → ℝ) (hx : x ∈ closedBall x₀ (a / 2)) : ‖f x‖ ≤ L := by
    calc ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖f x₀‖ := by
        gcongr
        exact hl.norm_sub_le (hball hx).1 (mem_of_mem_nhds hs)
      _ ≤ K * a + ‖f x₀‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self ha.le) hx
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  set ε := a / L / 8 with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨ε, hε0, ⟨a / 2, by positivity⟩, ⟨a / 4, by positivity⟩, ⟨L, hL0.le⟩, K,
    by change (0 : ℝ) < a / 4; positivity, ?_, ?_⟩
  · intro x hx
    exact (hball hx).2
  · apply IsPicardLindelof.of_time_independent
    · intro x hx; exact hb x hx
    · exact hl.mono fun x hx => (hball hx).1
    · change L * max (ε - 0) (0 - -ε) ≤ a / 2 - a / 4
      simp only [sub_zero, zero_sub, neg_neg, max_self]
      rw [hε]
      have : L * (a / L / 8) = a / 8 := by field_simp
      rw [this]
      linarith

/-- The local flow near `x₀ ∈ M`. -/
lemma local_flow (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ M) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : (Fin n → ℝ) → ℝ → Fin n → ℝ,
      (∀ x ∈ closedBall x₀ r, α x 0 = x ∧ IsSol f M (Ioo (-ε) ε) (α x)) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Ioo (-ε) ε, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  classical
  obtain ⟨ε, hε, a, r, L, K, hr, haM, hpl⟩ := exists_picard hM hf hx₀
  have hex (x) (hx : x ∈ closedBall x₀ (r : ℝ)) := ODE.FunSpace.exists_isFixedPt_next hpl hx
  choose α hα using hex
  set β : (Fin n → ℝ) → ℝ → Fin n → ℝ := fun x =>
    if hx : x ∈ closedBall x₀ (r : ℝ) then (α x hx).compProj else fun _ => x with hβ
  refine ⟨r, hr, ε, hε, β, fun x hx => ⟨?_, fun t ht => ⟨?_, ?_⟩⟩, ?_⟩
  · simp only [hβ, dif_pos hx]
    have h1 : (α x hx).compProj 0 = (α x hx) ⟨0, by constructor <;> linarith⟩ :=
      ODE.FunSpace.compProj_of_mem _
    rw [h1]
    nth_rw 1 [← hα x hx]
    exact ODE.FunSpace.next_apply₀ hpl hx _
  · simp only [hβ, dif_pos hx]
    exact haM ((α x hx).compProj_mem_closedBall hpl.mul_max_le)
  · simp only [hβ, dif_pos hx]
    have hIcc : Icc (-ε) ε ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hd : HasDerivWithinAt (α x hx).compProj (f ((α x hx).compProj t)) (Icc (-ε) ε) t := by
      rw [ODE.FunSpace.compProj_apply]
      apply ODE.hasDerivWithinAt_picard_Icc (⟨0, by constructor <;> linarith⟩ : Icc (-ε) ε).2
        hpl.continuousOn_uncurry (α x hx).continuous_compProj.continuousOn
        (fun _ _ => (α x hx).compProj_mem_closedBall hpl.mul_max_le) x
        (Ioo_subset_Icc_self ht) |>.congr_of_mem _ (Ioo_subset_Icc_self ht)
      intro t' ht'
      nth_rw 1 [← hα x hx]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
    exact hd.hasDerivAt hIcc
  · obtain ⟨L', h⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hpl
    refine ⟨L', fun t ht => LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    simp only [hβ, dif_pos hx, dif_pos hy]
    rw [ODE.FunSpace.compProj_apply, ODE.FunSpace.compProj_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc (-ε) ε) := ⟨⟨0, by constructor <;> linarith⟩⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

/-- Uniform local existence near `x₀ ∈ M`, phrased for `flow`. -/
lemma local_flow' (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ M) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      (∀ x ∈ closedBall x₀ r, Ioo (-ε) ε ⊆ lifetime f M x) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Ioo (-ε) ε, LipschitzOnWith L' (flow f M t) (closedBall x₀ r) := by
  obtain ⟨r, hr, ε, hε, α, hα, L', hL'⟩ := local_flow hM hf hx₀
  have hIo : IsOpen (Ioo (-ε) ε) := isOpen_Ioo
  have hIc : (Ioo (-ε) ε).OrdConnected := ordConnected_Ioo
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have heq : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Ioo (-ε) ε, flow f M t x = α x t := fun x hx t ht =>
    flow_eq_of_sol hM hf hIo hIc h0 ht (hα x hx).1 (hα x hx).2
  refine ⟨r, hr, ε, hε, fun x hx t ht => ⟨_, α x, hIo, hIc, h0, ht, (hα x hx).1, (hα x hx).2⟩,
    L', fun t ht => ?_⟩
  intro x hx y hy
  rw [heq x hx t ht, heq y hy t ht]
  exact hL' t ht hx hy

lemma zero_mem_lifetime (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (hx : x ∈ M) : (0 : ℝ) ∈ lifetime f M x := by
  obtain ⟨r, hr, ε, hε, h, -⟩ := local_flow' hM hf hx
  exact h x (mem_closedBall_self hr.le) ⟨by linarith, hε⟩

lemma flow_zero' (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} (hx : x ∈ M) :
    flow f M 0 x = x := flow_zero hM hf (zero_mem_lifetime hM hf hx)

end PBF


/-! Continuity of the flow on its (open) domain, and completeness of orbits staying in a compact
subset of `M` (Teschl, Theorem 6.1 and Lemma 6.3). -/

open Set Filter Topology Metric Function
open scoped NNReal

namespace PBF

open TeschlODE.Planar

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {M : Set (Fin n → ℝ)}

/-- `t` is a good time for `x₀`: `Φ(t, ·)` is defined near `x₀` and continuous at `x₀`. -/
def Good (f : (Fin n → ℝ) → Fin n → ℝ) (M : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) (t : ℝ) : Prop :=
  (∀ᶠ y in 𝓝 x₀, t ∈ lifetime f M y) ∧ ContinuousAt (fun y => flow f M t y) x₀

lemma good_step (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ c : Fin n → ℝ} {t s r ε : ℝ}
    {L' : ℝ≥0} (hloc : ∀ x ∈ closedBall c r, Ioo (-ε) ε ⊆ lifetime f M x)
    (hL : ∀ τ ∈ Ioo (-ε) ε, LipschitzOnWith L' (flow f M τ) (closedBall c r))
    (hg : Good f M x₀ t) (ht : flow f M t x₀ ∈ ball c r) (hs : s - t ∈ Ioo (-ε) ε) :
    Good f M x₀ s := by
  have hV : ∀ᶠ y in 𝓝 x₀, t ∈ lifetime f M y ∧ flow f M t y ∈ ball c r :=
    hg.1.and (hg.2.preimage_mem_nhds (isOpen_ball.mem_nhds ht))
  have hV' : ∀ᶠ y in 𝓝 x₀, s ∈ lifetime f M y ∧
      flow f M s y = flow f M (s - t) (flow f M t y) := by
    filter_upwards [hV] with y hy
    have h1 : s - t ∈ lifetime f M (flow f M t y) :=
      hloc _ (ball_subset_closedBall hy.2) hs
    have h2 : s - t + t ∈ lifetime f M y := (mem_lifetime_flow hM hf hy.1).mp h1
    rw [sub_add_cancel] at h2
    refine ⟨h2, ?_⟩
    rw [flow_flow hM hf hy.1 (by rwa [sub_add_cancel]), sub_add_cancel]
  refine ⟨hV'.mono fun y hy => hy.1, ?_⟩
  have hc : ContinuousAt (flow f M (s - t)) (flow f M t x₀) :=
    ((hL _ hs).continuousOn).continuousAt
      (closedBall_mem_nhds_of_mem (mem_ball.mp ht))
  have := hc.comp hg.2
  exact this.congr (hV'.mono fun y hy => hy.2.symm)

lemma good_zero (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ M) :
    Good f M x₀ 0 := by
  have hev : ∀ᶠ y in 𝓝 x₀, y ∈ M := hM.mem_nhds hx₀
  refine ⟨hev.mono fun y hy => zero_mem_lifetime hM hf hy, ?_⟩
  exact continuousAt_id.congr (hev.mono fun y hy => (flow_zero' hM hf hy).symm)

/-- Every nonnegative time in the lifetime is good. -/
lemma good_of_nonneg (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ : Fin n → ℝ} {b : ℝ}
    (hb : b ∈ lifetime f M x₀) (hb0 : 0 ≤ b) : Good f M x₀ b := by
  have hx₀ : x₀ ∈ M := mem_of_mem_lifetime hb
  have h0 : (0 : ℝ) ∈ lifetime f M x₀ := zero_mem_lifetime_of_mem hb
  have hIcc : Icc 0 b ⊆ lifetime f M x₀ := (ordConnected_lifetime x₀).out h0 hb
  by_contra hbad
  set A := {t | t ∈ Icc 0 b ∧ ¬ Good f M x₀ t}
  have hAne : A.Nonempty := ⟨b, ⟨hb0, le_rfl⟩, hbad⟩
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set ts := sInf A
  have hts0 : 0 ≤ ts := le_csInf hAne fun t ht => ht.1.1
  have htsb : ts ≤ b := csInf_le hAbdd ⟨⟨hb0, le_rfl⟩, hbad⟩
  have htsL : ts ∈ lifetime f M x₀ := hIcc ⟨hts0, htsb⟩
  have hbelow : ∀ t ∈ Ico 0 ts, Good f M x₀ t := by
    intro t ht
    by_contra hg
    have : ts ≤ t := csInf_le hAbdd ⟨⟨ht.1, ht.2.le.trans htsb⟩, hg⟩
    linarith [ht.2]
  -- local flow at `Φ(ts, x₀)`
  set p := flow f M ts x₀
  have hp : p ∈ M := flow_mem hM hf htsL
  obtain ⟨r, hr, ε, hε, hloc, L', hL⟩ := local_flow' hM hf hp
  -- `ts` is good
  have hgts : Good f M x₀ ts := by
    rcases hts0.eq_or_lt with h | h
    · rw [← h]; exact good_zero hM hf hx₀
    · have hcont : ContinuousAt (fun t => flow f M t x₀) ts :=
        ((flow_sol hM hf x₀) ts htsL).2.continuousAt
      have hev : ∀ᶠ t in 𝓝 ts, flow f M t x₀ ∈ ball p r :=
        hcont.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
      have hev' : ∀ᶠ t in 𝓝[<] ts, flow f M t x₀ ∈ ball p r ∧ t ∈ Ioo (max 0 (ts - ε)) ts :=
        (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT (max_lt h (by linarith)))
      obtain ⟨t, ht1, ht2⟩ := hev'.exists
      exact good_step hM hf hloc hL (hbelow t ⟨(le_max_left _ _).trans ht2.1.le, ht2.2⟩) ht1
        ⟨by linarith [ht2.2], by linarith [le_max_right 0 (ts - ε), ht2.1]⟩
  -- a neighbourhood above `ts` is good
  obtain ⟨a, haA, hats⟩ := exists_lt_of_csInf_lt hAne (show ts < ts + ε by linarith)
  have hle : ts ≤ a := csInf_le hAbdd haA
  exact haA.2 (good_step hM hf hloc hL hgts (mem_ball_self hr)
    ⟨by linarith, by linarith⟩)

lemma good_of_mem (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ : Fin n → ℝ} {b : ℝ}
    (hb : b ∈ lifetime f M x₀) : Good f M x₀ b := by
  rcases le_total 0 b with h | h
  · exact good_of_nonneg hM hf hb h
  · have hb' : -b ∈ lifetime (fun y => -f y) M x₀ := mem_lifetime_neg.mpr (by simpa using hb)
    obtain ⟨h1, h2⟩ := good_of_nonneg hM hf.neg hb' (by linarith)
    have hev : ∀ᶠ y in 𝓝 x₀, b ∈ lifetime f M y :=
      h1.mono fun y hy => by simpa using mem_lifetime_neg.mp hy
    refine ⟨hev, h2.congr (hev.mono fun y hy => ?_)⟩
    show flow (fun x => -f x) M (-b) y = flow f M b y
    rw [flow_neg hM hf (by rw [neg_neg]; exact hy), neg_neg]

/-- The flow is continuous on its domain, and the domain is open (Teschl, Theorem 6.1). -/
theorem flow_cont (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ : Fin n → ℝ} {t₀ : ℝ}
    (h : t₀ ∈ lifetime f M x₀) :
    (∀ᶠ q in 𝓝 (t₀, x₀), q.1 ∈ lifetime f M q.2) ∧
      ContinuousAt (fun q : ℝ × (Fin n → ℝ) => flow f M q.1 q.2) (t₀, x₀) := by
  obtain ⟨hg1, hg2⟩ := good_of_mem hM hf h
  set p := flow f M t₀ x₀
  have hp : p ∈ M := flow_mem hM hf h
  obtain ⟨r, hr, ε, hε, hloc, L', hL⟩ := local_flow' hM hf hp
  -- joint continuity of the local flow
  have hF : ContinuousOn (fun q : ℝ × (Fin n → ℝ) => flow f M q.1 q.2)
      (Ioo (-ε) ε ×ˢ closedBall p r) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ L'
    · intro τ hτ; exact hL τ hτ
    · intro z hz
      exact ((flow_sol hM hf z).continuousOn).mono (hloc z hz)
  have hV : ∀ᶠ y in 𝓝 x₀, t₀ ∈ lifetime f M y ∧ flow f M t₀ y ∈ ball p r :=
    hg1.and (hg2.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)))
  have hW : ∀ᶠ q in 𝓝 (t₀, x₀), q.1 - t₀ ∈ Ioo (-ε) ε ∧
      (t₀ ∈ lifetime f M q.2 ∧ flow f M t₀ q.2 ∈ ball p r) := by
    have h1 : ∀ᶠ q : ℝ × (Fin n → ℝ) in 𝓝 (t₀, x₀), q.1 - t₀ ∈ Ioo (-ε) ε := by
      have : ContinuousAt (fun q : ℝ × (Fin n → ℝ) => q.1 - t₀) (t₀, x₀) := by fun_prop
      exact this.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simp [hε]))
    exact h1.and ((continuous_snd.tendsto (t₀, x₀)).eventually hV)
  have hW' : ∀ᶠ q in 𝓝 (t₀, x₀), q.1 ∈ lifetime f M q.2 ∧
      flow f M q.1 q.2 = flow f M (q.1 - t₀) (flow f M t₀ q.2) := by
    filter_upwards [hW] with q hq
    have h1 : q.1 - t₀ ∈ lifetime f M (flow f M t₀ q.2) :=
      hloc _ (ball_subset_closedBall hq.2.2) hq.1
    have h2 := (mem_lifetime_flow hM hf hq.2.1).mp h1
    rw [sub_add_cancel] at h2
    refine ⟨h2, ?_⟩
    rw [flow_flow hM hf hq.2.1 (by rwa [sub_add_cancel]), sub_add_cancel]
  refine ⟨hW'.mono fun q hq => hq.1, ?_⟩
  have hFa : ContinuousAt (fun q : ℝ × (Fin n → ℝ) => flow f M q.1 q.2) (0, p) :=
    hF.continuousAt (prod_mem_nhds (isOpen_Ioo.mem_nhds (by simp [hε]))
      (closedBall_mem_nhds p hr))
  have hinner : ContinuousAt (fun q : ℝ × (Fin n → ℝ) => (q.1 - t₀, flow f M t₀ q.2)) (t₀, x₀) :=
    (continuousAt_fst.sub continuousAt_const).prodMk
      (ContinuousAt.comp (g := fun y => flow f M t₀ y) (f := Prod.snd) hg2
        continuous_snd.continuousAt)
  have hcomp : ContinuousAt ((fun q : ℝ × (Fin n → ℝ) => flow f M q.1 q.2) ∘
      (fun q : ℝ × (Fin n → ℝ) => (q.1 - t₀, flow f M t₀ q.2))) (t₀, x₀) := by
    apply ContinuousAt.comp _ hinner
    simpa using hFa
  exact hcomp.congr (hW'.mono fun q hq => hq.2.symm)

lemma continuousAt_flow_right (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ : Fin n → ℝ}
    {t : ℝ} (h : t ∈ lifetime f M x₀) : ContinuousAt (fun y => flow f M t y) x₀ :=
  (good_of_mem hM hf h).2

lemma eventually_mem_lifetime (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x₀ : Fin n → ℝ}
    {t : ℝ} (h : t ∈ lifetime f M x₀) : ∀ᶠ y in 𝓝 x₀, t ∈ lifetime f M y :=
  (good_of_mem hM hf h).1

/-- If the forward orbit stays in a compact subset of `M`, the point is forward complete
(Teschl, Lemma 6.3). -/
lemma complete_of_compact (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (hx : x ∈ M) {C : Set (Fin n → ℝ)} (hC : IsCompact C) (hCM : C ⊆ M)
    (horb : ∀ t ∈ lifetime f M x, 0 ≤ t → flow f M t x ∈ C) : Ici 0 ⊆ lifetime f M x := by
  have h0 : (0 : ℝ) ∈ lifetime f M x := zero_mem_lifetime hM hf hx
  by_contra hne
  obtain ⟨T, hT0, hT⟩ := not_subset.mp hne
  -- `T⁺ = sup` of the nonnegative lifetime
  set A := {t | 0 ≤ t ∧ t ∈ lifetime f M x}
  have hAne : A.Nonempty := ⟨0, le_rfl, h0⟩
  have hAbdd : BddAbove A := by
    refine ⟨T, fun t ht => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hT ((ordConnected_lifetime x).out h0 ht.2 ⟨hT0, hlt.le⟩)
  set Tp := sSup A
  have hTpA : ∀ t, 0 ≤ t → t < Tp → t ∈ lifetime f M x := by
    intro t ht0 htT
    obtain ⟨a, haA, hta⟩ := exists_lt_of_lt_csSup hAne htT
    exact (ordConnected_lifetime x).out h0 haA.2 ⟨ht0, hta.le⟩
  have hTp0 : 0 ≤ Tp := le_csSup hAbdd ⟨le_rfl, h0⟩
  have hTpL : Tp ∉ lifetime f M x := by
    intro hTp
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_lifetime x) Tp hTp
    have : Tp + δ / 2 ∈ A := ⟨by linarith, hball (by
      rw [Real.ball_eq_Ioo]; constructor <;> linarith)⟩
    linarith [le_csSup hAbdd this]
  have hTppos : 0 < Tp := by
    rcases hTp0.eq_or_lt with h | h
    · exact absurd (h ▸ h0) hTpL
    · exact h
  -- a sequence of times increasing to `T⁺`
  set u : ℕ → ℝ := fun k => Tp - Tp / (k + 2)
  have hu0 : ∀ k, 0 ≤ u k := fun k => by
    simp only [u]
    have : Tp / (k + 2) ≤ Tp := div_le_self hTp0 (by linarith [k.cast_nonneg (α := ℝ)])
    linarith
  have huT : ∀ k, u k < Tp := fun k => by
    simp only [u]
    have : 0 < Tp / (k + 2) := by positivity
    linarith
  have huL : ∀ k, u k ∈ lifetime f M x := fun k => hTpA _ (hu0 k) (huT k)
  have hulim : Tendsto u atTop (𝓝 Tp) := by
    have : Tendsto (fun k : ℕ => Tp / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := Tp)).sub this
  obtain ⟨z, hzC, φ, hφ, hlim⟩ := hC.tendsto_subseq fun k => horb _ (huL k) (hu0 k)
  obtain ⟨r, hr, ε, hε, hloc, -⟩ := local_flow' hM hf (hCM hzC)
  have hev1 : ∀ᶠ k in atTop, flow f M (u (φ k)) x ∈ closedBall z r :=
    hlim.eventually (closedBall_mem_nhds z hr)
  have hev2 : ∀ᶠ k in atTop, Tp - ε / 2 < u (φ k) :=
    (hulim.comp hφ.tendsto_atTop).eventually (lt_mem_nhds (by linarith))
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  have h1 : ε / 2 ∈ lifetime f M (flow f M (u (φ k)) x) :=
    hloc _ hk1 ⟨by linarith, by linarith⟩
  have h2 := (mem_lifetime_flow hM hf (huL _)).mp h1
  have : ε / 2 + u (φ k) ∈ A := ⟨by linarith [hu0 (φ k)], h2⟩
  linarith [le_csSup hAbdd this]

end PBF


/-! Orbits, periodic points and `ω`-limit sets of `TeschlODE.Planar.flow`. -/

open Set Filter Topology Metric Function
open scoped NNReal

namespace PBF

open TeschlODE.Planar

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {M : Set (Fin n → ℝ)}

/-! ### Time reversal of the derived notions -/

lemma lifetime_neg_eq (x : Fin n → ℝ) :
    lifetime (fun y => -f y) M x = {t | -t ∈ lifetime f M x} := by
  ext t; exact mem_lifetime_neg

lemma halfOrbit_neg (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (σ : Bool) (x : Fin n → ℝ) :
    halfOrbit (fun y => -f y) M σ x = halfOrbit f M (!σ) x := by
  ext z
  constructor
  · rintro ⟨t, ⟨ht, hσ⟩, rfl⟩
    have ht' : -t ∈ lifetime f M x := mem_lifetime_neg.mp ht
    refine ⟨-t, ⟨ht', ?_⟩, (flow_neg hM hf ht').symm⟩
    cases σ <;> simp_all
  · rintro ⟨t, ⟨ht, hσ⟩, rfl⟩
    have ht' : -t ∈ lifetime (fun y => -f y) M x := mem_lifetime_neg.mpr (by simpa using ht)
    refine ⟨-t, ⟨ht', ?_⟩, ?_⟩
    · cases σ <;> simp_all
    · beta_reduce
      rw [flow_neg hM hf (by rw [neg_neg]; exact ht), neg_neg]

lemma orbit_neg (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (x : Fin n → ℝ) :
    orbit (fun y => -f y) M x = orbit f M x := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : -t ∈ lifetime f M x := mem_lifetime_neg.mp ht
    exact ⟨-t, ht', (flow_neg hM hf ht').symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨-t, mem_lifetime_neg.mpr (by simpa using ht), ?_⟩
    beta_reduce
    rw [flow_neg hM hf (by rw [neg_neg]; exact ht), neg_neg]

lemma tendsto_neg_iff_atTop_atBot {u : ℕ → ℝ} :
    Tendsto (fun k => -u k) atTop atBot ↔ Tendsto u atTop atTop := by
  constructor
  · intro h
    have := tendsto_neg_atBot_atTop.comp h
    simpa [Function.comp_def] using this
  · intro h; exact tendsto_neg_atTop_atBot.comp h

lemma tendsto_neg_iff_atBot_atTop {u : ℕ → ℝ} :
    Tendsto (fun k => -u k) atTop atTop ↔ Tendsto u atTop atBot := by
  constructor
  · intro h
    have := tendsto_neg_atTop_atBot.comp h
    simpa [Function.comp_def] using this
  · intro h; exact tendsto_neg_atBot_atTop.comp h

lemma omega_neg (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (σ : Bool) (x : Fin n → ℝ) :
    omegaLimitSet (fun y => -f y) M σ x = omegaLimitSet f M (!σ) x := by
  ext y
  constructor
  · rintro ⟨hy, u, hu, hlim, hconv⟩
    have hu' : ∀ k, -u k ∈ lifetime f M x := fun k => mem_lifetime_neg.mp (hu k)
    refine ⟨hy, fun k => -u k, hu', ?_, ?_⟩
    · cases σ <;>
        simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true]
          at hlim ⊢ <;>
        first
        | exact tendsto_neg_iff_atBot_atTop.mpr hlim
        | exact tendsto_neg_iff_atTop_atBot.mpr hlim
    · refine hconv.congr fun k => ?_
      exact flow_neg hM hf (hu' k)
  · rintro ⟨hy, u, hu, hlim, hconv⟩
    have hu' : ∀ k, -u k ∈ lifetime (fun y => -f y) M x :=
      fun k => mem_lifetime_neg.mpr (by simpa using hu k)
    refine ⟨hy, fun k => -u k, hu', ?_, ?_⟩
    · cases σ <;>
        simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true]
          at hlim ⊢ <;>
        first
        | exact tendsto_neg_iff_atBot_atTop.mpr hlim
        | exact tendsto_neg_iff_atTop_atBot.mpr hlim
    · refine hconv.congr fun k => ?_
      rw [flow_neg hM hf (by simpa using hu k), neg_neg]

/-! ### Fixed points -/

lemma fixed_sol {x : Fin n → ℝ} (hx : x ∈ M) (hfx : f x = 0) :
    IsSol f M univ (fun _ => x) := fun _ _ => ⟨hx, by rw [hfx]; exact hasDerivAt_const _ _⟩

lemma mem_lifetime_of_fixed {x : Fin n → ℝ} (hx : x ∈ M) (hfx : f x = 0) (t : ℝ) :
    t ∈ lifetime f M x :=
  ⟨univ, fun _ => x, isOpen_univ, ordConnected_univ, trivial, trivial, rfl, fixed_sol hx hfx⟩

lemma flow_of_fixed (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} (hx : x ∈ M)
    (hfx : f x = 0) (t : ℝ) : flow f M t x = x :=
  flow_eq_of_sol hM hf isOpen_univ ordConnected_univ trivial trivial rfl (fixed_sol hx hfx)

lemma fixed_of_flow_fixed (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {t : ℝ}
    (ht : t ∈ lifetime f M x) (hfx : f (flow f M t x) = 0) : f x = 0 := by
  set y := flow f M t x
  have hy : y ∈ M := flow_mem hM hf ht
  have h1 : -t ∈ lifetime f M y := (mem_lifetime_flow hM hf ht).mpr (by
    simpa using zero_mem_lifetime_of_mem ht)
  have h2 : flow f M (-t) y = x := by
    rw [flow_flow hM hf ht (by simpa using zero_mem_lifetime_of_mem ht), neg_add_cancel,
      flow_zero hM hf (zero_mem_lifetime_of_mem ht)]
  rw [← h2, flow_of_fixed hM hf hy hfx]
  exact hfx

lemma regular_flow (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {t : ℝ}
    (ht : t ∈ lifetime f M x) (hfx : f x ≠ 0) : f (flow f M t x) ≠ 0 :=
  fun h => hfx (fixed_of_flow_fixed hM hf ht h)

/-! ### Orbits -/

lemma orbit_eq_of_mem (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x y : Fin n → ℝ}
    (hy : y ∈ orbit f M x) : orbit f M y = orbit f M x := by
  obtain ⟨s, hs, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' := (mem_lifetime_flow hM hf hs).mp ht
    exact ⟨t + s, ht', (flow_flow hM hf hs ht').symm⟩
  · rintro ⟨t, ht, rfl⟩
    have ht' : t - s ∈ lifetime f M (flow f M s x) :=
      (mem_lifetime_flow hM hf hs).mpr (by simpa using ht)
    refine ⟨t - s, ht', ?_⟩
    beta_reduce
    rw [flow_flow hM hf hs (by simpa using ht), sub_add_cancel]

lemma mem_orbit_self (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} (hx : x ∈ M) :
    x ∈ orbit f M x := ⟨0, zero_mem_lifetime hM hf hx, flow_zero' hM hf hx⟩

lemma orbit_subset_M (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (x : Fin n → ℝ) :
    orbit f M x ⊆ M := by
  rintro _ ⟨t, ht, rfl⟩; exact flow_mem hM hf ht

/-! ### Periodic points -/

lemma periodic_of_eq (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {a b : ℝ}
    (ha : a ∈ lifetime f M x) (hb : b ∈ lifetime f M x) (hab : a < b)
    (heq : flow f M a x = flow f M b x) : IsPeriodicPoint f M x := by
  have h0 : (0 : ℝ) ∈ lifetime f M x := zero_mem_lifetime_of_mem ha
  -- `T = b - a`
  have hT : b - a ∈ lifetime f M x := by
    have h1 : -a ∈ lifetime f M (flow f M b x) := by
      rw [← heq]; exact (mem_lifetime_flow hM hf ha).mpr (by simpa using h0)
    have := (mem_lifetime_flow hM hf hb).mp h1
    simpa [sub_eq_neg_add, add_comm] using this
  refine ⟨b - a, by linarith, hT, ?_⟩
  have e1 : flow f M (-a) (flow f M b x) = flow f M (b - a) x := by
    rw [flow_flow hM hf hb (by simpa [sub_eq_neg_add, add_comm] using hT)]
    ring_nf
  have e2 : flow f M (-a) (flow f M a x) = x := by
    rw [flow_flow hM hf ha (by simpa using h0), neg_add_cancel, flow_zero hM hf h0]
  rw [← e1, ← heq, e2]

lemma periodic_lifetime (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (hx : IsPeriodicPoint f M x) : ∃ T > 0, lifetime f M x = univ ∧
      ∀ t, flow f M (t + T) x = flow f M t x := by
  obtain ⟨T, hT, hTL, hTx⟩ := hx
  set L := lifetime f M x
  have hshift : ∀ t, t ∈ L ↔ t + T ∈ L := by
    intro t
    have := mem_lifetime_flow hM hf hTL (t := t)
    rw [hTx] at this
    exact this
  have hZ : ∀ k : ℕ, (k : ℝ) * T ∈ L ∧ -((k : ℝ) * T) ∈ L := by
    intro k
    induction k with
    | zero => simpa using zero_mem_lifetime_of_mem hTL
    | succ k ih =>
      refine ⟨?_, ?_⟩
      · have := (hshift _).mp ih.1
        simpa [add_mul] using this
      · have := (hshift (-(((k : ℝ) + 1) * T))).mpr (by
          have : -(((k : ℝ) + 1) * T) + T = -((k : ℝ) * T) := by ring
          rw [this]; exact ih.2)
        simpa using this
  have hL : L = univ := by
    refine eq_univ_of_forall fun t => ?_
    obtain ⟨k, hk⟩ := exists_nat_gt (|t| / T)
    have hk' : |t| < k * T := by rwa [div_lt_iff₀ hT] at hk
    exact (ordConnected_lifetime x).out (hZ k).2 (hZ k).1
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨T, hT, hL, fun t => ?_⟩
  have := flow_flow hM hf hTL (t := t) (by rw [show lifetime f M x = univ from hL]; trivial)
  rw [hTx] at this
  exact this.symm

lemma periodic_mem_lifetime (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (hx : IsPeriodicPoint f M x) (t : ℝ) : t ∈ lifetime f M x := by
  obtain ⟨T, -, hL, -⟩ := periodic_lifetime hM hf hx
  rw [hL]; trivial

lemma periodic_orbit_eq (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (hx : IsPeriodicPoint f M x) : ∃ T > 0, orbit f M x = (fun t => flow f M t x) '' Icc 0 T := by
  obtain ⟨T, hT, hL, hper⟩ := periodic_lifetime hM hf hx
  refine ⟨T, hT, ?_⟩
  have hP : Periodic (fun t => flow f M t x) T := hper
  have := hP.image_Icc hT 0
  rw [zero_add] at this
  rw [this, orbit, hL, image_univ]

lemma isCompact_orbit_of_periodic (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (hx : IsPeriodicPoint f M x) : IsCompact (orbit f M x) := by
  obtain ⟨T, hT, h⟩ := periodic_orbit_eq hM hf hx
  rw [h]
  apply isCompact_Icc.image_of_continuousOn
  refine ((flow_sol hM hf x).continuousOn).mono fun t _ => periodic_mem_lifetime hM hf hx t

lemma periodic_of_mem_orbit (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x y : Fin n → ℝ}
    (hx : IsPeriodicPoint f M x) (hy : y ∈ orbit f M x) : IsPeriodicPoint f M y := by
  obtain ⟨T, hT, hL, hper⟩ := periodic_lifetime hM hf hx
  obtain ⟨s, hs, rfl⟩ := hy
  refine ⟨T, hT, (mem_lifetime_flow hM hf hs).mpr (by rw [hL]; trivial), ?_⟩
  rw [flow_flow hM hf hs (by rw [hL]; trivial), add_comm, hper]

lemma halfOrbit_subset_orbit (σ : Bool) (x : Fin n → ℝ) : halfOrbit f M σ x ⊆ orbit f M x := by
  rintro _ ⟨t, ⟨ht, -⟩, rfl⟩; exact ⟨t, ht, rfl⟩

/-! ### `ω`-limit sets (forward) -/

lemma omega_true_iff {x y : Fin n → ℝ} :
    y ∈ omegaLimitSet f M true x ↔ y ∈ M ∧ ∀ ε > 0, ∀ T : ℝ, ∃ t, T ≤ t ∧
      t ∈ lifetime f M x ∧ dist (flow f M t x) y < ε := by
  constructor
  · rintro ⟨hy, u, hu, hlim, hconv⟩
    refine ⟨hy, fun ε hε T => ?_⟩
    simp only [if_true] at hlim
    obtain ⟨k, hk1, hk2⟩ := ((hlim.eventually (eventually_ge_atTop T)).and
      (hconv.eventually (ball_mem_nhds y hε))).exists
    exact ⟨u k, hk1, hu k, hk2⟩
  · rintro ⟨hy, h⟩
    choose t ht using fun k : ℕ => h (1 / (k + 1)) (by positivity) k
    refine ⟨hy, t, fun k => (ht k).2.1, ?_, ?_⟩
    · simp only [if_true]
      exact tendsto_atTop_mono (fun k => (ht k).1) tendsto_natCast_atTop_atTop
    · rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ => dist_nonneg) (fun k => (ht k).2.2.le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma omega_true_closed {x z : Fin n → ℝ} (hz : z ∈ M)
    (h : ∀ ε > 0, ∃ w ∈ omegaLimitSet f M true x, dist w z < ε) :
    z ∈ omegaLimitSet f M true x := by
  refine omega_true_iff.mpr ⟨hz, fun ε hε T => ?_⟩
  obtain ⟨w, hw, hwz⟩ := h (ε / 2) (by linarith)
  obtain ⟨t, hT, ht, htw⟩ := (omega_true_iff.mp hw).2 (ε / 2) (by linarith) T
  exact ⟨t, hT, ht, by linarith [dist_triangle (flow f M t x) w z]⟩

lemma omega_true_complete {x y : Fin n → ℝ} (hy : y ∈ omegaLimitSet f M true x) :
    Ici 0 ⊆ lifetime f M x := by
  intro t ht
  obtain ⟨-, h⟩ := omega_true_iff.mp hy
  obtain ⟨s, hs, hsL, -⟩ := h 1 one_pos t
  exact (ordConnected_lifetime x).out (zero_mem_lifetime_of_mem hsL) hsL ⟨ht, hs⟩

lemma omega_true_invariant (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x y : Fin n → ℝ}
    (hy : y ∈ omegaLimitSet f M true x) {t : ℝ} (ht : t ∈ lifetime f M y) :
    flow f M t y ∈ omegaLimitSet f M true x := by
  have hcomp := omega_true_complete hy
  obtain ⟨hyM, h⟩ := omega_true_iff.mp hy
  obtain ⟨hev, hcont⟩ := flow_cont hM hf ht
  refine omega_true_iff.mpr ⟨flow_mem hM hf ht, fun ε hε T => ?_⟩
  -- a neighbourhood of `y` on which `Φ(t, ·)` is defined and `ε`-close
  have hnb : ∀ᶠ z in 𝓝 y, t ∈ lifetime f M z ∧ dist (flow f M t z) (flow f M t y) < ε := by
    have h1 : ∀ᶠ z in 𝓝 y, t ∈ lifetime f M z :=
      (continuous_const.prodMk continuous_id).continuousAt.eventually hev
    have h2 : ContinuousAt (fun z => flow f M t z) y :=
      hcont.comp (continuous_const.prodMk continuous_id).continuousAt
    exact h1.and (h2.eventually (ball_mem_nhds _ hε))
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨s, hs, hsL, hsd⟩ := h δ hδ (max T (T - t))
  have hz := hδb hsd
  have hts : t + s ∈ lifetime f M x := (mem_lifetime_flow hM hf hsL).mp hz.1
  refine ⟨t + s, ?_, hts, ?_⟩
  · have : T - t ≤ s := le_trans (le_max_right _ _) hs
    linarith
  · rw [← flow_flow hM hf hsL hts]; exact hz.2

lemma omega_true_orbit_subset (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x y : Fin n → ℝ}
    (hy : y ∈ omegaLimitSet f M true x) : orbit f M y ⊆ omegaLimitSet f M true x := by
  rintro _ ⟨t, ht, rfl⟩; exact omega_true_invariant hM hf hy ht

lemma omega_true_of_omega_true (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x y z : Fin n → ℝ}
    (hy : y ∈ omegaLimitSet f M true x) (hz : z ∈ omegaLimitSet f M true y) :
    z ∈ omegaLimitSet f M true x := by
  obtain ⟨hzM, h⟩ := omega_true_iff.mp hz
  refine omega_true_closed hzM fun ε hε => ?_
  obtain ⟨t, -, ht, htd⟩ := h ε hε 0
  exact ⟨_, omega_true_invariant hM hf hy ht, htd⟩

lemma omega_true_of_orbit (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x y z : Fin n → ℝ}
    (hy : y ∈ orbit f M x) : z ∈ omegaLimitSet f M true y ↔ z ∈ omegaLimitSet f M true x := by
  obtain ⟨s, hs, rfl⟩ := hy
  simp only [omega_true_iff]
  constructor
  · rintro ⟨hzM, h⟩
    refine ⟨hzM, fun ε hε T => ?_⟩
    obtain ⟨t, hT, ht, hd⟩ := h ε hε (T - s)
    have hts := (mem_lifetime_flow hM hf hs).mp ht
    exact ⟨t + s, by linarith, hts, by rwa [← flow_flow hM hf hs hts]⟩
  · rintro ⟨hzM, h⟩
    refine ⟨hzM, fun ε hε T => ?_⟩
    obtain ⟨t, hT, ht, hd⟩ := h ε hε (T + s)
    have hts : t - s ∈ lifetime f M (flow f M s x) :=
      (mem_lifetime_flow hM hf hs).mpr (by simpa using ht)
    refine ⟨t - s, by linarith, hts, ?_⟩
    rw [flow_flow hM hf hs (by simpa using ht), sub_add_cancel]; exact hd

lemma omega_true_periodic (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (hx : IsPeriodicPoint f M x) : omegaLimitSet f M true x = orbit f M x := by
  obtain ⟨T, hT, hL, hper⟩ := periodic_lifetime hM hf hx
  have hP : Periodic (fun t => flow f M t x) T := hper
  ext y
  constructor
  · intro hy
    have hcl : IsClosed (orbit f M x) := (isCompact_orbit_of_periodic hM hf hx).isClosed
    rw [← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, -, ht, hd⟩ := (omega_true_iff.mp hy).2 ε hε 0
    exact ⟨_, ⟨t, ht, rfl⟩, by rw [dist_comm]; exact hd⟩
  · rintro ⟨s, hs, rfl⟩
    refine omega_true_iff.mpr ⟨flow_mem hM hf hs, fun ε hε T' => ?_⟩
    obtain ⟨m, hm⟩ := exists_nat_gt ((T' - s) / T)
    rw [div_lt_iff₀ hT] at hm
    refine ⟨s + m * T, by linarith, by rw [hL]; trivial, ?_⟩
    have : flow f M (s + m * T) x = flow f M s x := (hP.nat_mul m) s
    rw [this, dist_self]; exact hε

end PBF


/-! A compact forward `ω`-limit set is connected. -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {M : Set (Fin n → ℝ)}

theorem omega_true_preconnected (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (hc : IsCompact (omegaLimitSet f M true x)) :
    IsPreconnected (omegaLimitSet f M true x) := by
  set Ω := omegaLimitSet f M true x
  rw [isPreconnected_closed_iff]
  intro u v hu hv hsub ⟨a, haΩ, hau⟩ ⟨b, hbΩ, hbv⟩
  by_contra hdisj
  rw [not_nonempty_iff_eq_empty] at hdisj
  set A := Ω ∩ u
  set B := Ω ∩ v
  have hA : IsCompact A := hc.inter_right hu
  have hB : IsCompact B := hc.inter_right hv
  have hAne : A.Nonempty := ⟨a, haΩ, hau⟩
  have hΩM : Ω ⊆ M := fun y hy => hy.1
  have hAB : ∀ y ∈ B, y ∉ A := fun y hyB hyA => by
    have : y ∈ Ω ∩ (u ∩ v) := ⟨hyA.1, hyA.2, hyB.2⟩
    rw [hdisj] at this; exact this
  -- `B` is at positive distance from `A`
  have hposB : ∀ y ∈ B, 0 < infDist y A := fun y hy =>
    (infDist_pos_iff_notMem_closure hAne).mp (by rw [hA.isClosed.closure_eq]; exact hAB y hy)
  obtain ⟨d0, hd0, hd0B⟩ : ∃ d0 > 0, ∀ y ∈ B, d0 ≤ infDist y A := by
    obtain ⟨y0, hy0, hmin⟩ := hB.exists_isMinOn ⟨b, hbΩ, hbv⟩
      (continuous_infDist_pt A).continuousOn
    exact ⟨infDist y0 A, hposB y0 hy0, fun y hy => hmin hy⟩
  -- a closed neighbourhood of `A` inside `M`
  obtain ⟨ρ, hρ, hρM⟩ := hA.exists_cthickening_subset_open hM (inter_subset_left.trans hΩM)
  have hnear : ∀ z, infDist z A ≤ ρ → z ∈ cthickening ρ A := by
    intro z hz
    obtain ⟨y, hy, hyd⟩ := hA.exists_infDist_eq_dist hAne z
    exact mem_cthickening_of_dist_le z y ρ A hy (hyd ▸ hz)
  set δ := min (d0 / 2) ρ
  have hδ : 0 < δ := lt_min (by linarith) hρ
  set S := {z | infDist z A = δ}
  have hScl : IsClosed S := isClosed_eq (continuous_infDist_pt A) continuous_const
  have hSsub : S ⊆ cthickening ρ A := fun z hz => hnear z (by
    rw [show infDist z A = δ from hz]; exact min_le_right _ _)
  have hScpt : IsCompact S := hA.cthickening.of_isClosed_subset hScl hSsub
  have hSM : S ⊆ M := hSsub.trans hρM
  -- the orbit crosses `S` at arbitrarily late times
  have hcross : ∀ T : ℝ, ∃ t, T ≤ t ∧ t ∈ lifetime f M x ∧ flow f M t x ∈ S := by
    intro T
    have hcomp := omega_true_complete haΩ
    obtain ⟨t1, hT1, ht1L, ht1⟩ := (omega_true_iff.mp haΩ).2 δ hδ (max T 0)
    have hη : 0 < infDist b A - δ := by
      have := hd0B b ⟨hbΩ, hbv⟩
      have : δ ≤ d0 / 2 := min_le_left _ _
      linarith
    obtain ⟨t2, hT2, ht2L, ht2⟩ := (omega_true_iff.mp hbΩ).2 (infDist b A - δ) hη t1
    have hg1 : infDist (flow f M t1 x) A ≤ δ := by
      have := infDist_le_dist_of_mem (x := flow f M t1 x) hau
      have : infDist (flow f M t1 x) A ≤ dist (flow f M t1 x) a :=
        infDist_le_dist_of_mem ⟨haΩ, hau⟩
      linarith
    have hg2 : δ ≤ infDist (flow f M t2 x) A := by
      have := infDist_le_infDist_add_dist (x := b) (y := flow f M t2 x) (s := A)
      rw [dist_comm] at this
      linarith
    have hcont : ContinuousOn (fun t => infDist (flow f M t x) A) (Icc t1 t2) := by
      refine (continuous_infDist_pt A).comp_continuousOn ?_
      refine ((flow_sol hM hf x).continuousOn).mono fun t ht => hcomp ?_
      exact le_trans (le_trans (le_max_right T 0) hT1) ht.1
    obtain ⟨t, ht, htS⟩ := intermediate_value_Icc hT2 hcont ⟨hg1, hg2⟩
    exact ⟨t, le_trans (le_max_left T 0) (hT1.trans ht.1),
      hcomp (le_trans (le_max_right T 0) (hT1.trans ht.1)), htS⟩
  choose t ht using fun k : ℕ => hcross k
  obtain ⟨z, hzS, φ, hφ, hlim⟩ := hScpt.tendsto_subseq fun k => (ht k).2.2
  have hzΩ : z ∈ Ω := by
    refine omega_true_iff.mpr ⟨hSM hzS, fun ε hε T => ?_⟩
    obtain ⟨N, hN⟩ := exists_nat_ge T
    obtain ⟨k, hk1, hk2⟩ := ((hφ.tendsto_atTop.eventually (eventually_ge_atTop N)).and
      (hlim.eventually (ball_mem_nhds z hε))).exists
    exact ⟨t (φ k), le_trans hN (le_trans (Nat.cast_le.mpr hk1) (ht (φ k)).1),
      (ht (φ k)).2.1, hk2⟩
  rcases hsub hzΩ with hzu | hzv
  · have h0 : infDist z A = 0 := infDist_zero_of_mem ⟨hzΩ, hzu⟩
    have : infDist z A = δ := hzS
    linarith
  · have h1 := hd0B z ⟨hzΩ, hzv⟩
    have : infDist z A = δ := hzS
    have : δ ≤ d0 / 2 := min_le_left _ _
    linarith

end PBF


/-! Charts at a transversal arc and the crossing lemma (Teschl, Lemma 6.9, `C⁰` version). -/

open Set Filter Topology Metric Function
open scoped NNReal

namespace PBF

open TeschlODE.Planar

/-- The linear map `(a, b) ↦ a • v + b • w`. -/
noncomputable def lin2 (v w : Fin 2 → ℝ) : ℝ × ℝ →L[ℝ] (Fin 2 → ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w

lemma lin2_apply (v w : Fin 2 → ℝ) (z : ℝ × ℝ) : lin2 v w z = z.1 • v + z.2 • w := by
  simp [lin2]

lemma lin2_injective {v w : Fin 2 → ℝ} (h : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    Function.Injective (lin2 v w) := by
  intro z z' hz
  rw [lin2_apply, lin2_apply] at hz
  have e0 := congrFun hz 0
  have e1 := congrFun hz 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
  have h1 : (z.1 - z'.1) * (v 0 * w 1 - v 1 * w 0) = 0 := by
    linear_combination w 1 * e0 - w 0 * e1
  have h2 : (z.2 - z'.2) * (v 0 * w 1 - v 1 * w 0) = 0 := by
    linear_combination v 0 * e1 - v 1 * e0
  have a1 := (mul_eq_zero.mp h1).resolve_right h
  have a2 := (mul_eq_zero.mp h2).resolve_right h
  exact Prod.ext (by linarith) (by linarith)

/-- `lin2 v w` as a continuous linear equivalence. -/
noncomputable def lin2Equiv {v w : Fin 2 → ℝ} (h : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  (LinearEquiv.ofBijective (lin2 v w : ℝ × ℝ →ₗ[ℝ] Fin 2 → ℝ)
    ⟨lin2_injective h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_prod])).mp (lin2_injective h)⟩).toContinuousLinearEquiv

lemma lin2Equiv_coe {v w : Fin 2 → ℝ} (h : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    ((lin2Equiv h : (ℝ × ℝ) →L[ℝ] (Fin 2 → ℝ))) = lin2 v w := by
  ext z <;> rfl

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

/-- Chart at a point `p = s u₀` of a transversal arc: a `C¹` function `S` vanishing exactly on
the arc near `p`, with `DS(p) f(p) = 1`, and the coordinates `(U, S)` of the inverse of
`(u, t) ↦ s u + t f(p)`. -/
theorem arc_chart (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ}
    {s : ℝ → Fin 2 → ℝ} (harc : IsTransversalArc f M J s) {u₀ : ℝ} (hu₀ : u₀ ∈ J) :
    ∃ (S U : (Fin 2 → ℝ) → ℝ) (ρ η : ℝ), 0 < ρ ∧ 0 < η ∧ ball (s u₀) ρ ⊆ M ∧
      Icc (u₀ - η) (u₀ + η) ⊆ J ∧
      (∀ q ∈ ball (s u₀) ρ, q = s (U q) + S q • f (s u₀) ∧ |U q - u₀| < η ∧ |S q| < η) ∧
      (∀ u t, |u - u₀| < η → |t| < η → U (s u + t • f (s u₀)) = u ∧
        S (s u + t • f (s u₀)) = t) ∧
      (∀ q ∈ ball (s u₀) ρ, (q ∈ s '' J ↔ S q = 0)) ∧
      (∀ q ∈ ball (s u₀) ρ, ContDiffAt ℝ 1 S q) ∧ ContinuousOn U (ball (s u₀) ρ) ∧
      S (s u₀) = 0 ∧ U (s u₀) = u₀ ∧ fderiv ℝ S (s u₀) (f (s u₀)) = 1 := by
  obtain ⟨hJo, hJc, -, hsC, hemb, hsM, htr⟩ := harc
  set p := s u₀
  set w := f p
  set v := deriv s u₀
  have hdet : v 0 * w 1 - v 1 * w 0 ≠ 0 := (htr u₀ hu₀).2
  -- the map `ψ (u, t) = s u + t • w`
  set ψ : ℝ × ℝ → Fin 2 → ℝ := fun z => s z.1 + z.2 • w with hψ
  have hsCa : ContDiffAt ℝ 1 s u₀ := hsC.contDiffAt (hJo.mem_nhds hu₀)
  have hψC : ContDiffAt ℝ 1 ψ (u₀, 0) :=
    (hsCa.comp (u₀, 0) contDiffAt_fst).add (contDiffAt_snd.smul contDiffAt_const)
  have hsd : HasDerivAt s v u₀ := (hsCa.differentiableAt one_ne_zero).hasDerivAt
  have hψD : HasFDerivAt ψ (lin2Equiv hdet : (ℝ × ℝ) →L[ℝ] (Fin 2 → ℝ)) (u₀, 0) := by
    rw [lin2Equiv_coe]
    have h1 : HasFDerivAt (fun z : ℝ × ℝ => s z.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v) (u₀, 0) := by
      have hfst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ)
          ((u₀, (0 : ℝ)) : ℝ × ℝ) := hasFDerivAt_fst
      have hs' : HasFDerivAt s ((1 : ℝ →L[ℝ] ℝ).smulRight v) (Prod.fst ((u₀, (0 : ℝ)) : ℝ × ℝ)) :=
        hsd.hasFDerivAt
      have := hs'.comp ((u₀, (0 : ℝ)) : ℝ × ℝ) hfst
      exact this.congr_fderiv (by ext z <;> simp)
    have h2 : HasFDerivAt (fun z : ℝ × ℝ => z.2 • w)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w) (u₀, 0) :=
      (hasFDerivAt_snd (p := ((u₀, 0) : ℝ × ℝ))).smul_const w
    exact h1.add h2
  set e := hψC.toOpenPartialHomeomorph ψ hψD one_ne_zero
  have hψp : ψ (u₀, 0) = p := by simp [hψ, p]
  have hsrc : (u₀, 0) ∈ e.source := hψC.mem_toOpenPartialHomeomorph_source hψD one_ne_zero
  have htgt : p ∈ e.target := by
    rw [← hψp]; exact hψC.image_mem_toOpenPartialHomeomorph_target hψD one_ne_zero
  have hinv : ContDiffAt ℝ 1 e.symm p := by
    have := hψC.to_localInverse hψD one_ne_zero
    rw [hψp] at this
    exact this
  have hep : e.symm p = (u₀, 0) := by
    rw [← hψp]; exact e.left_inv hsrc
  have hDinv : HasFDerivAt e.symm
      ((lin2Equiv hdet).symm : (Fin 2 → ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    have := (hψC.hasStrictFDerivAt' hψD one_ne_zero).to_localInverse
    rw [hψp] at this
    exact this.hasFDerivAt
  set S : (Fin 2 → ℝ) → ℝ := fun q => (e.symm q).2
  set U : (Fin 2 → ℝ) → ℝ := fun q => (e.symm q).1
  -- choose `η` with the closed `η`-rectangle in the source and the parameters in `J`
  obtain ⟨η₁, hη₁, hη₁J⟩ := Metric.isOpen_iff.mp hJo u₀ hu₀
  have hsrcN : e.source ∈ 𝓝 ((u₀, 0) : ℝ × ℝ) := e.open_source.mem_nhds hsrc
  obtain ⟨η₂, hη₂, hη₂s⟩ := Metric.mem_nhds_iff.mp hsrcN
  -- embedding: points of the arc near `p` have parameters near `u₀`
  have hembN : ∀ η > 0, ∀ᶠ q in 𝓝 p, ∀ u ∈ J, s u = q → |u - u₀| < η := by
    intro η hη
    have hind := hemb.isInducing
    have hset : {z : J | |(z : ℝ) - u₀| < η} ∈ 𝓝 (⟨u₀, hu₀⟩ : J) := by
      apply IsOpen.mem_nhds
      · exact isOpen_lt (continuous_abs.comp (continuous_subtype_val.sub continuous_const))
          continuous_const
      · simp [hη]
    rw [hind.nhds_eq_comap] at hset
    obtain ⟨V, hV, hVsub⟩ := hset
    filter_upwards [hV] with q hq u hu hsu
    have : (⟨u, hu⟩ : J) ∈ (fun z : J => s z) ⁻¹' V := by simp [hsu, hq]
    exact hVsub this
  set η := min (η₁ / 2) (η₂ / 2)
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηJ : Icc (u₀ - η) (u₀ + η) ⊆ J := by
    intro u hu
    apply hη₁J
    rw [Real.ball_eq_Ioo]
    have : η ≤ η₁ / 2 := min_le_left _ _
    constructor <;> linarith [hu.1, hu.2]
  have hrect : ∀ u t, |u - u₀| < η → |t| < η → ((u, t) : ℝ × ℝ) ∈ e.source := by
    intro u t hu ht
    apply hη₂s
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    have : η ≤ η₂ / 2 := min_le_right _ _
    exact max_lt (by linarith) (by linarith)
  -- eventual properties at `p`
  have hev1 : ∀ᶠ q in 𝓝 p, q ∈ e.target := e.open_target.mem_nhds htgt
  have hev2 : ∀ᶠ q in 𝓝 p, |U q - u₀| < η ∧ |S q| < η := by
    have hc : ContinuousAt e.symm p := hinv.continuousAt
    have : ∀ᶠ z in 𝓝 ((u₀, 0) : ℝ × ℝ), |z.1 - u₀| < η ∧ |z.2| < η := by
      have h1 : ∀ᶠ z in 𝓝 ((u₀, 0) : ℝ × ℝ), |z.1 - u₀| < η :=
        (continuous_abs.comp (continuous_fst.sub continuous_const)).continuousAt.eventually
          (gt_mem_nhds (by simp [hη]))
      have h2 : ∀ᶠ z in 𝓝 ((u₀, 0) : ℝ × ℝ), |z.2| < η :=
        (continuous_abs.comp continuous_snd).continuousAt.eventually
          (gt_mem_nhds (by simp [hη]))
      exact h1.and h2
    rw [← hep] at this
    exact hc.eventually this
  have hev3 : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 1 e.symm q := hinv.eventually (by simp)
  have hev4 : ∀ᶠ q in 𝓝 p, q ∈ M := hM.mem_nhds (hsM u₀ hu₀)
  have hev5 := hembN η hη
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff_ball.mp
    ((((hev1.and hev2).and hev3).and hev4).and hev5)
  refine ⟨S, U, ρ, η, hρ, hη, fun q hq => (hρb q hq).1.2, hηJ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩ := hρb q hq
    refine ⟨?_, h2⟩
    have := e.right_inv h1
    exact this.symm
  · intro u t hu ht
    have := e.left_inv (hrect u t hu ht)
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · intro q hq
    obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩ := hρb q hq
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' := h5 u hu rfl
      have := e.left_inv (hrect u 0 hu' (by simp [hη]))
      have h' : e (u, 0) = s u := by
        show ψ (u, 0) = s u
        simp [hψ]
      rw [h'] at this
      exact congrArg Prod.snd this
    · intro hS
      have := e.right_inv h1
      refine ⟨U q, hηJ ⟨by linarith [(abs_lt.mp h2.1).1], by linarith [(abs_lt.mp h2.1).2]⟩, ?_⟩
      have h' : e (e.symm q) = s (U q) + S q • w := rfl
      rw [h', hS, zero_smul, add_zero] at this
      exact this
  · intro q hq
    exact contDiffAt_snd.comp q (hρb q hq).1.1.2
  · intro q hq
    exact (contDiffAt_fst.comp q (hρb q hq).1.1.2).continuousAt.continuousWithinAt
  · show (e.symm p).2 = 0
    rw [hep]
  · show (e.symm p).1 = u₀
    rw [hep]
  · have hS : HasFDerivAt S ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((lin2Equiv hdet).symm : (Fin 2 → ℝ) →L[ℝ] (ℝ × ℝ))) p :=
      (hasFDerivAt_snd).comp p hDinv
    rw [hS.fderiv]
    have hw : (lin2Equiv hdet).symm w = (0, 1) := by
      rw [ContinuousLinearEquiv.symm_apply_eq]
      show w = (lin2Equiv hdet : (ℝ × ℝ) →L[ℝ] (Fin 2 → ℝ)) (0, 1)
      rw [lin2Equiv_coe, lin2_apply]
      simp
    simp [hw]

end PBF


/-! The crossing lemma: near a point of a transversal arc, every orbit crosses the arc exactly
once in a short time interval, and the crossing time depends continuously on the point
(Teschl, Lemma 6.9). -/

open Set Filter Topology Metric Function
open scoped NNReal

namespace PBF

open TeschlODE.Planar

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

/-- A chart at the point `s u₀` of a transversal arc. -/
structure ArcChart (f : (Fin 2 → ℝ) → Fin 2 → ℝ) (M : Set (Fin 2 → ℝ)) (J : Set ℝ)
    (s : ℝ → Fin 2 → ℝ) (u₀ : ℝ) where
  S : (Fin 2 → ℝ) → ℝ
  U : (Fin 2 → ℝ) → ℝ
  ρ : ℝ
  η : ℝ
  hρ : 0 < ρ
  hη : 0 < η
  ballM : ball (s u₀) ρ ⊆ M
  IccJ : Icc (u₀ - η) (u₀ + η) ⊆ J
  rep : ∀ q ∈ ball (s u₀) ρ, q = s (U q) + S q • f (s u₀) ∧ |U q - u₀| < η ∧ |S q| < η
  leftInv : ∀ u t, |u - u₀| < η → |t| < η →
    U (s u + t • f (s u₀)) = u ∧ S (s u + t • f (s u₀)) = t
  zero_iff : ∀ q ∈ ball (s u₀) ρ, (q ∈ s '' J ↔ S q = 0)
  smooth : ∀ q ∈ ball (s u₀) ρ, ContDiffAt ℝ 1 S q
  contU : ContinuousOn U (ball (s u₀) ρ)
  S_p : S (s u₀) = 0
  U_p : U (s u₀) = u₀
  deriv_p : fderiv ℝ S (s u₀) (f (s u₀)) = 1

theorem exists_arcChart (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ}
    {s : ℝ → Fin 2 → ℝ} (harc : IsTransversalArc f M J s) {u₀ : ℝ} (hu₀ : u₀ ∈ J) :
    Nonempty (ArcChart f M J s u₀) := by
  obtain ⟨S, U, ρ, η, hρ, hη, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    arc_chart hM hf harc hu₀
  exact ⟨⟨S, U, ρ, η, hρ, hη, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩⟩

namespace ArcChart

variable {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} {u₀ : ℝ}

/-- Monotone crossing data near `s u₀`. -/
theorem cross (C : ArcChart f M J s u₀) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) :
    ∃ δ > 0, ∃ ρ' > 0, ρ' ≤ C.ρ ∧ ∀ y ∈ ball (s u₀) ρ',
      Icc (-δ) δ ⊆ lifetime f M y ∧ (∀ t ∈ Icc (-δ) δ, flow f M t y ∈ ball (s u₀) C.ρ) ∧
      StrictMonoOn (fun t => C.S (flow f M t y)) (Icc (-δ) δ) ∧
      C.S (flow f M (-δ) y) < 0 ∧ 0 < C.S (flow f M δ y) := by
  set p := s u₀
  have hpM : p ∈ M := C.ballM (mem_ball_self C.hρ)
  have h0p : (0 : ℝ) ∈ lifetime f M p := zero_mem_lifetime hM hf hpM
  have hfp : flow f M 0 p = p := flow_zero' hM hf hpM
  obtain ⟨hdom, hcont⟩ := flow_cont hM hf h0p
  -- `g (t, y) = DS(Φ(t,y)) f(Φ(t,y))` is close to `1` near `(0, p)`
  have hSd : ContinuousAt (fderiv ℝ C.S) p :=
    (C.smooth p (mem_ball_self C.hρ)).continuousAt_fderiv one_ne_zero
  have hfc : ContinuousAt f p := hf.continuousOn.continuousAt (hM.mem_nhds hpM)
  have hg : ContinuousAt (fun q : ℝ × (Fin 2 → ℝ) =>
      fderiv ℝ C.S (flow f M q.1 q.2) (f (flow f M q.1 q.2))) (0, p) := by
    apply ContinuousAt.clm_apply
    · exact ContinuousAt.comp (g := fderiv ℝ C.S) (by simpa [hfp] using hSd) hcont
    · exact ContinuousAt.comp (g := f) (by simpa [hfp] using hfc) hcont
  have hg0 : fderiv ℝ C.S (flow f M (0 : ℝ) p) (f (flow f M (0 : ℝ) p)) = 1 := by
    rw [hfp]; exact C.deriv_p
  have hev : ∀ᶠ q in 𝓝 ((0 : ℝ), p), q.1 ∈ lifetime f M q.2 ∧
      flow f M q.1 q.2 ∈ ball p C.ρ ∧
      1 / 2 < fderiv ℝ C.S (flow f M q.1 q.2) (f (flow f M q.1 q.2)) := by
    refine hdom.and (Filter.Eventually.and ?_ ?_)
    · exact hcont.eventually (isOpen_ball.mem_nhds (by
        show flow f M 0 p ∈ ball p C.ρ
        rw [hfp]; exact mem_ball_self C.hρ))
    · exact hg.eventually (lt_mem_nhds (by
        show (1 : ℝ) / 2 < fderiv ℝ C.S (flow f M 0 p) (f (flow f M 0 p))
        rw [hg0]; norm_num))
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff.mp hev
  have hbox : ∀ t y, |t| < r → dist y p < r → t ∈ lifetime f M y ∧
      flow f M t y ∈ ball p C.ρ ∧
      1 / 2 < fderiv ℝ C.S (flow f M t y) (f (flow f M t y)) := by
    intro t y ht hy
    have hd : dist ((t, y) : ℝ × (Fin 2 → ℝ)) ((0 : ℝ), p) < r := by
      rw [Prod.dist_eq, Real.dist_eq, sub_zero]
      exact max_lt ht hy
    exact hrb hd
  set δ := r / 2 with hδdef
  have hδ : 0 < δ := by positivity
  -- derivative of `t ↦ S(Φ(t, y))`
  have hderiv : ∀ y, dist y p < r → ∀ t, |t| < r →
      HasDerivAt (fun t => C.S (flow f M t y))
        (fderiv ℝ C.S (flow f M t y) (f (flow f M t y))) t := by
    intro y hy t ht
    obtain ⟨h1, h2, -⟩ := hbox t y ht hy
    have hS : HasFDerivAt C.S (fderiv ℝ C.S (flow f M t y)) (flow f M t y) :=
      ((C.smooth _ h2).differentiableAt one_ne_zero).hasFDerivAt
    exact hS.comp_hasDerivAt t ((flow_sol hM hf y) t h1).2
  have hmono : ∀ y, dist y p < r → StrictMonoOn (fun t => C.S (flow f M t y)) (Icc (-δ) δ) := by
    intro y hy
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t ht
      have : |t| < r := by
        rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, hδdef, hr]
      exact (hderiv y hy t this).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have : |t| < r := by
        rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, hδdef, hr]
      rw [(hderiv y hy t this).deriv]
      have := (hbox t y this hy).2.2
      linarith
  -- signs at `±δ` for `y = p`, then nearby
  have hδr : |δ| < r := by rw [abs_of_pos hδ]; linarith [hδdef]
  have hδr' : |-δ| < r := by rw [abs_neg, abs_of_pos hδ]; linarith [hδdef]
  have hpS0 : C.S (flow f M 0 p) = 0 := by rw [hfp]; exact C.S_p
  have hp_mem : dist p p < r := by rw [dist_self]; exact hr
  have hneg : C.S (flow f M (-δ) p) < 0 := by
    have := hmono p hp_mem ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩
      (show -δ < 0 by linarith)
    simpa [hpS0] using this
  have hpos : 0 < C.S (flow f M δ p) := by
    have := hmono p hp_mem ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩
      (show (0 : ℝ) < δ by linarith)
    simpa [hpS0] using this
  have hcS : ∀ t, |t| < r → ContinuousAt (fun y => C.S (flow f M t y)) p := by
    intro t ht
    obtain ⟨h1, h2, -⟩ := hbox t p ht hp_mem
    exact ((C.smooth _ h2).continuousAt).comp (continuousAt_flow_right hM hf h1)
  have hev2 : ∀ᶠ y in 𝓝 p, C.S (flow f M (-δ) y) < 0 ∧ 0 < C.S (flow f M δ y) :=
    ((hcS _ hδr').eventually (gt_mem_nhds hneg)).and
      ((hcS _ hδr).eventually (lt_mem_nhds hpos))
  obtain ⟨r2, hr2, hr2b⟩ := Metric.eventually_nhds_iff.mp hev2
  set ρ' := min (min r r2) C.ρ
  have hρ' : 0 < ρ' := lt_min (lt_min hr hr2) C.hρ
  refine ⟨δ, hδ, ρ', hρ', min_le_right _ _, fun y hy => ?_⟩
  have hyr : dist y p < r := lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_left _ _))
  have hyr2 : dist y p < r2 := lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_right _ _))
  have hIcc : ∀ t ∈ Icc (-δ) δ, |t| < r := fun t ht => by
    rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, hδdef, hr]
  refine ⟨fun t ht => (hbox t y (hIcc t ht) hyr).1, fun t ht => (hbox t y (hIcc t ht) hyr).2.1,
    hmono y hyr, (hr2b hyr2).1, (hr2b hyr2).2⟩

/-- The crossing lemma: unique crossing in a short time interval. -/
theorem crossing (C : ArcChart f M J s u₀) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) :
    ∃ δ > 0, ∃ ρ' > 0, ∀ y ∈ ball (s u₀) ρ', Icc (-δ) δ ⊆ lifetime f M y ∧
      ∃ τ ∈ Ioo (-δ) δ, flow f M τ y ∈ s '' J ∧
        ∀ t ∈ Icc (-δ) δ, flow f M t y ∈ s '' J → t = τ := by
  obtain ⟨δ, hδ, ρ', hρ', hρρ, h⟩ := C.cross hM hf
  refine ⟨δ, hδ, ρ', hρ', fun y hy => ?_⟩
  obtain ⟨hL, hball, hmono, hneg, hpos⟩ := h y hy
  have hcont : ContinuousOn (fun t => C.S (flow f M t y)) (Icc (-δ) δ) := by
    intro t ht
    have h2 := hball t ht
    exact (ContinuousAt.comp (g := C.S) (f := fun t => flow f M t y) (C.smooth _ h2).continuousAt
      ((flow_sol hM hf y) t (hL ht)).2.continuousAt).continuousWithinAt
  obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc (by linarith) hcont ⟨hneg.le, hpos.le⟩
  have hτ' : τ ∈ Ioo (-δ) δ := by
    refine ⟨lt_of_le_of_ne hτ.1 ?_, lt_of_le_of_ne hτ.2 ?_⟩
    · rintro rfl; simp only at hτ0; linarith
    · rintro rfl; simp only at hτ0; linarith
  refine ⟨hL, τ, hτ', (C.zero_iff _ (hball τ hτ)).mpr hτ0, fun t ht hts => ?_⟩
  have ht0 : C.S (flow f M t y) = 0 := (C.zero_iff _ (hball t ht)).mp hts
  exact hmono.injOn ht hτ (ht0.trans hτ0.symm)

/-- Crossing times near `s u₀` are small. -/
theorem crossing_small (C : ArcChart f M J s u₀) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ y in 𝓝 (s u₀), ∃ τ ∈ Ioo (-ε) ε,
      τ ∈ lifetime f M y ∧ flow f M τ y ∈ s '' J := by
  obtain ⟨δ, hδ, ρ', hρ', hρρ, h⟩ := C.cross hM hf
  set ε' := min (ε / 2) δ
  have hε' : 0 < ε' := lt_min (by linarith) hδ
  have hε'δ : ε' ≤ δ := min_le_right _ _
  set p := s u₀
  have hpM : p ∈ M := C.ballM (mem_ball_self C.hρ)
  have hfp : flow f M 0 p = p := flow_zero' hM hf hpM
  obtain ⟨hLp, hballp, hmonop, -, -⟩ := h p (mem_ball_self hρ')
  have hpS0 : C.S (flow f M 0 p) = 0 := by rw [hfp]; exact C.S_p
  have hneg : C.S (flow f M (-ε') p) < 0 := by
    have := hmonop ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (show -ε' < 0 by linarith)
    simpa [hpS0] using this
  have hpos : 0 < C.S (flow f M ε' p) := by
    have := hmonop ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (show (0 : ℝ) < ε' by linarith)
    simpa [hpS0] using this
  have hcS : ∀ t ∈ Icc (-δ) δ, ContinuousAt (fun y => C.S (flow f M t y)) p := by
    intro t ht
    exact ((C.smooth _ (hballp t ht)).continuousAt).comp
      (continuousAt_flow_right hM hf (hLp ht))
  have hev : ∀ᶠ y in 𝓝 p, y ∈ ball p ρ' ∧ C.S (flow f M (-ε') y) < 0 ∧
      0 < C.S (flow f M ε' y) :=
    (isOpen_ball.eventually_mem (mem_ball_self hρ')).and
      (((hcS _ ⟨by linarith, by linarith⟩).eventually (gt_mem_nhds hneg)).and
        ((hcS _ ⟨by linarith, by linarith⟩).eventually (lt_mem_nhds hpos)))
  filter_upwards [hev] with y ⟨hy, hn, hp⟩
  obtain ⟨hL, hball, -, -, -⟩ := h y hy
  have hsub : Icc (-ε') ε' ⊆ Icc (-δ) δ := Icc_subset_Icc (by linarith) hε'δ
  have hcont : ContinuousOn (fun t => C.S (flow f M t y)) (Icc (-ε') ε') := by
    intro t ht
    have h2 := hball t (hsub ht)
    exact (ContinuousAt.comp (g := C.S) (f := fun t => flow f M t y) (C.smooth _ h2).continuousAt
      ((flow_sol hM hf y) t (hL (hsub ht))).2.continuousAt).continuousWithinAt
  obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc (by linarith) hcont ⟨hn.le, hp.le⟩
  refine ⟨τ, ⟨by linarith [hτ.1, min_le_left (ε / 2) δ], by linarith [hτ.2, min_le_left (ε / 2) δ]⟩,
    hL (hsub hτ), (C.zero_iff _ (hball τ (hsub hτ))).mpr hτ0⟩

end ArcChart

end PBF


/-! Transversal arcs: basic facts, existence of a straight transversal arc through a regular point,
crossing of nearby orbits, and crossings of an orbit near points of its `ω`-limit set. Also the
`σ`-general forms of the `ω`-limit set facts, obtained by time reversal. -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

section arcs

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

lemma arc_neg {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} (h : IsTransversalArc f M J s) :
    IsTransversalArc (fun y => -f y) M J s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun t ht => ⟨(h7 t ht).1, ?_⟩⟩
  have hne := (h7 t ht).2
  have heq : deriv s t 0 * (fun y => -f y) (s t) 1 - deriv s t 1 * (fun y => -f y) (s t) 0 =
      -(deriv s t 0 * f (s t) 1 - deriv s t 1 * f (s t) 0) := by
    simp only [Pi.neg_apply]; ring
  rw [heq]; exact neg_ne_zero.mpr hne

lemma arc_neg_iff {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} :
    IsTransversalArc (fun y => -f y) M J s ↔ IsTransversalArc f M J s := by
  refine ⟨fun h => ?_, arc_neg⟩
  have := arc_neg h
  simpa only [neg_neg] using this

lemma arc_reg {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} (h : IsTransversalArc f M J s) {t : ℝ}
    (ht : t ∈ J) : f (s t) ≠ 0 := by
  intro h0
  apply (h.2.2.2.2.2.2 t ht).2
  simp [h0]

lemma arc_mem {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} (h : IsTransversalArc f M J s) {t : ℝ}
    (ht : t ∈ J) : s t ∈ M := h.2.2.2.2.2.1 t ht

lemma arc_injOn {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} (h : IsTransversalArc f M J s) : InjOn s J := by
  intro a ha b hb hab
  have := h.2.2.2.2.1.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab
  exact congrArg Subtype.val this

lemma arc_inv_cont {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} (h : IsTransversalArc f M J s) {v : ℝ}
    (hv : v ∈ J) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ w ∈ J, dist (s w) (s v) < δ → |w - v| < ε := by
  have he := h.2.2.2.2.1
  have hnhds : Metric.ball (⟨v, hv⟩ : J) ε ∈ 𝓝 (⟨v, hv⟩ : J) := ball_mem_nhds _ hε
  rw [he.nhds_eq_comap, Filter.mem_comap] at hnhds
  obtain ⟨U, hU, hsub⟩ := hnhds
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, hδ, fun w hw hd => ?_⟩
  have hmem : (⟨w, hw⟩ : J) ∈ Metric.ball (⟨v, hv⟩ : J) ε := hsub (hball hd)
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hmem
  exact hmem

/-- A straight transversal arc through a regular point. -/
theorem exists_arc (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {y : Fin 2 → ℝ} (hy : y ∈ M)
    (hfy : f y ≠ 0) : ∃ (J : Set ℝ) (s : ℝ → Fin 2 → ℝ), IsTransversalArc f M J s ∧ y ∈ s '' J := by
  set w : Fin 2 → ℝ := ![-f y 1, f y 0] with hw
  have hw0 : w 0 = -f y 1 := rfl
  have hw1 : w 1 = f y 0 := rfl
  have hpos : 0 < f y 0 * f y 0 + f y 1 * f y 1 := by
    by_contra hle
    apply hfy
    have h0 : f y 0 = 0 := by nlinarith [mul_self_nonneg (f y 0), mul_self_nonneg (f y 1)]
    have h1 : f y 1 = 0 := by nlinarith [mul_self_nonneg (f y 0), mul_self_nonneg (f y 1)]
    funext i; fin_cases i <;> simp [h0, h1]
  have hcont : ContinuousAt (fun q => f y 0 * f q 0 + f y 1 * f q 1) y := by
    have hfc : ContinuousAt f y := hf.continuousOn.continuousAt (hM.mem_nhds hy)
    have h0 : ContinuousAt (fun q => f q 0) y := (continuous_apply 0).continuousAt.comp hfc
    have h1 : ContinuousAt (fun q => f q 1) y := (continuous_apply 1).continuousAt.comp hfc
    exact (continuousAt_const.mul h0).add (continuousAt_const.mul h1)
  have hev : ∀ᶠ q in 𝓝 y, q ∈ M ∧ 0 < f y 0 * f q 0 + f y 1 * f q 1 :=
    (hM.eventually_mem hy).and (hcont.eventually (lt_mem_nhds hpos))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set η := r / (‖w‖ + 1) with hηdef
  have hη : 0 < η := div_pos hr (by positivity)
  set s : ℝ → Fin 2 → ℝ := fun u => y + u • w with hsdef
  have hderiv : ∀ t, HasDerivAt s w t := fun t => by
    have h := ((hasDerivAt_id' t).smul_const w).const_add y
    rw [one_smul] at h
    exact h
  have hin : ∀ t ∈ Ioo (-η) η, dist (s t) y < r := by
    intro t ht
    have hlt : |t| < η := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hd : dist (s t) y = |t| * ‖w‖ := by
      simp [s, dist_eq_norm, norm_smul]
    rw [hd]
    have h1 : η * (‖w‖ + 1) = r := div_mul_cancel₀ r (by positivity)
    have h2 : |t| * ‖w‖ ≤ |t| * (‖w‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
    have h3 : |t| * (‖w‖ + 1) < η * (‖w‖ + 1) :=
      mul_lt_mul_of_pos_right hlt (by positivity)
    linarith
  set D := w 0 * w 0 + w 1 * w 1
  have hD : 0 < D := by simp only [D, hw0, hw1]; nlinarith
  set g : (Fin 2 → ℝ) → ℝ := fun q => ((q 0 - y 0) * w 0 + (q 1 - y 1) * w 1) / D
  have hgs : LeftInverse g s := by
    intro u
    simp only [g, s, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hgc : Continuous g := by
    simp only [g]
    fun_prop
  have hsc : Continuous s := by
    simp only [s]
    fun_prop
  have hemb : Topology.IsEmbedding s := hgs.isEmbedding hgc hsc
  have hwne : w ≠ 0 := by
    intro h0
    have : D = 0 := by simp [D, h0]
    linarith
  refine ⟨Ioo (-η) η, s, ⟨isOpen_Ioo, ordConnected_Ioo, ⟨0, by constructor <;> linarith⟩,
    ?_, hemb.comp Topology.IsEmbedding.subtypeVal, fun t ht => (hball (hin t ht)).1,
    fun t ht => ?_⟩, ⟨0, ⟨by linarith, hη⟩, by simp [s]⟩⟩
  · simp only [s]; fun_prop
  · rw [(hderiv t).deriv]
    refine ⟨hwne, ?_⟩
    have hq := (hball (hin t ht)).2
    rw [hw0, hw1]
    intro h0
    linarith

end arcs

end PBF


/-! Crossings near transversal arcs, `σ`-general `ω`-limit facts, and the abstract cores of
Teschl's Corollary 7.11, Lemmas 7.13–7.14 and Theorem 7.16: for a compact set `Ω` that contains
the orbits of its points and meets every transversal arc at most once (the property of
Corollary 7.10). -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

section general

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {M : Set (Fin n → ℝ)}

lemma periodic_neg (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ}
    (hx : IsPeriodicPoint f M x) : IsPeriodicPoint (fun y => -f y) M x := by
  obtain ⟨T, hT, hL, hper⟩ := periodic_lifetime hM hf hx
  have hx0 : (0 : ℝ) ∈ lifetime f M x := by rw [hL]; trivial
  refine ⟨T, hT, mem_lifetime_neg.mpr (by rw [hL]; trivial), ?_⟩
  rw [flow_neg hM hf (by rw [hL]; trivial)]
  have h := hper (-T)
  rw [neg_add_cancel, flow_zero hM hf hx0] at h
  exact h.symm

lemma periodic_neg_iff (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} :
    IsPeriodicPoint (fun y => -f y) M x ↔ IsPeriodicPoint f M x := by
  refine ⟨fun h => ?_, periodic_neg hM hf⟩
  have := periodic_neg hM hf.neg h
  simpa only [neg_neg] using this

lemma omega_false_eq (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (x : Fin n → ℝ) :
    omegaLimitSet f M false x = omegaLimitSet (fun y => -f y) M true x :=
  (omega_neg hM hf true x).symm

lemma omega_subset_M (σ : Bool) (x : Fin n → ℝ) : omegaLimitSet f M σ x ⊆ M := fun _ hy => hy.1

lemma omega_orbit_subset (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (σ : Bool) {x y : Fin n → ℝ}
    (hy : y ∈ omegaLimitSet f M σ x) : orbit f M y ⊆ omegaLimitSet f M σ x := by
  cases σ with
  | true => exact omega_true_orbit_subset hM hf hy
  | false =>
    rw [omega_false_eq hM hf] at hy ⊢
    rw [← orbit_neg hM hf]
    exact omega_true_orbit_subset hM hf.neg hy

lemma omega_periodic (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (σ : Bool) {x : Fin n → ℝ}
    (hx : IsPeriodicPoint f M x) : omegaLimitSet f M σ x = orbit f M x := by
  cases σ with
  | true => exact omega_true_periodic hM hf hx
  | false =>
    rw [omega_false_eq hM hf, omega_true_periodic hM hf.neg (periodic_neg hM hf hx),
      orbit_neg hM hf]

lemma omega_preconnected (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (σ : Bool) {x : Fin n → ℝ}
    (hc : IsCompact (omegaLimitSet f M σ x)) : IsPreconnected (omegaLimitSet f M σ x) := by
  cases σ with
  | true => exact omega_true_preconnected hM hf hc
  | false =>
    rw [omega_false_eq hM hf] at hc ⊢
    exact omega_true_preconnected hM hf.neg hc

/-- A forward orbit staying in a compact set `C ⊆ M` has a nonempty `ω₊`-limit set inside `C`. -/
lemma omega_true_sub (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} (hx : x ∈ M)
    {C : Set (Fin n → ℝ)} (hC : IsCompact C) (hCM : C ⊆ M)
    (horb : ∀ t ∈ lifetime f M x, 0 ≤ t → flow f M t x ∈ C) :
    (omegaLimitSet f M true x).Nonempty ∧ omegaLimitSet f M true x ⊆ C := by
  have hcomp := complete_of_compact hM hf hx hC hCM horb
  have hmem : ∀ k : ℕ, flow f M (k : ℝ) x ∈ C := fun k =>
    horb _ (hcomp (mem_Ici.mpr (Nat.cast_nonneg k))) (Nat.cast_nonneg k)
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hzC, φ, hφ, hlim⟩ := hC.tendsto_subseq hmem
    refine ⟨z, hCM hzC, fun k => (φ k : ℝ), fun k => hcomp (mem_Ici.mpr (Nat.cast_nonneg _)), ?_, hlim⟩
    exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  · intro y hy
    rw [← hC.isClosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, ht0, htL, hd⟩ := (omega_true_iff.mp hy).2 ε hε 0
    exact ⟨_, horb t htL ht0, by rw [dist_comm]; exact hd⟩

lemma omega_true_isClosed {x : Fin n → ℝ} {C : Set (Fin n → ℝ)} (hC : IsClosed C) (hCM : C ⊆ M)
    (hsub : omegaLimitSet f M true x ⊆ C) : IsClosed (omegaLimitSet f M true x) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  have hzC : z ∈ C := closure_minimal hsub hC hz
  refine omega_true_closed (hCM hzC) fun ε hε => ?_
  obtain ⟨w, hw, hd⟩ := Metric.mem_closure_iff.mp hz ε hε
  exact ⟨w, hw, by rw [dist_comm]; exact hd⟩

end general

lemma finite_preconnected_subsingleton {X : Type*} [TopologicalSpace X] [T1Space X] {S : Set X}
    (hS : S.Finite) (hc : IsPreconnected S) : S.Subsingleton := by
  intro a ha b hb
  by_contra hab
  have h1 : IsOpen (S \ {a})ᶜ := (hS.subset sdiff_subset).isClosed.isOpen_compl
  have h2 : IsOpen ({a}ᶜ : Set X) := isOpen_compl_singleton
  obtain ⟨z, hzS, hz1, hz2⟩ := hc _ _ h1 h2 (fun z _ => by
      by_cases hza : z = a
      · left; rintro ⟨-, h⟩; exact h hza
      · right; exact hza) ⟨a, ha, fun h => h.2 rfl⟩ ⟨b, hb, fun h => hab h.symm⟩
  exact hz1 ⟨hzS, hz2⟩

section planar

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

/-- Nearby orbits cross a transversal arc in short time, near the base point. -/
theorem cross_near (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ} {s : ℝ → Fin 2 → ℝ}
    (harc : IsTransversalArc f M J s) {u₀ : ℝ} (hu₀ : u₀ ∈ J) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, dist y (s u₀) < δ → ∃ τ, |τ| < ε ∧ τ ∈ lifetime f M y ∧
      flow f M τ y ∈ s '' J ∧ dist (flow f M τ y) (s u₀) < ε := by
  set z := s u₀
  have hz : z ∈ M := arc_mem harc hu₀
  have h0 : (0 : ℝ) ∈ lifetime f M z := zero_mem_lifetime hM hf hz
  obtain ⟨-, hc⟩ := flow_cont hM hf h0
  have hb : ball z ε ∈ 𝓝 ((fun q : ℝ × (Fin 2 → ℝ) => flow f M q.1 q.2) ((0 : ℝ), z)) := by
    simp only [flow_zero' hM hf hz]; exact ball_mem_nhds _ hε
  obtain ⟨δ1, hδ1, h1⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_mem hb)
  have hε' : 0 < min ε δ1 := lt_min hε hδ1
  obtain ⟨δ2, hδ2, h2⟩ := Metric.eventually_nhds_iff.mp
    ((exists_arcChart hM hf harc hu₀).some.crossing_small hM hf hε')
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hy => ?_⟩
  obtain ⟨τ, hτ, hτL, hτJ⟩ := h2 (lt_of_lt_of_le hy (min_le_right _ _))
  have hτa : |τ| < min ε δ1 := abs_lt.mpr ⟨hτ.1, hτ.2⟩
  refine ⟨τ, hτa.trans_le (min_le_left _ _), hτL, hτJ, ?_⟩
  have hd : dist ((τ, y) : ℝ × (Fin 2 → ℝ)) ((0 : ℝ), z) < δ1 := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero]
    exact ⟨hτa.trans_le (min_le_right _ _), lt_of_lt_of_le hy (min_le_left _ _)⟩
  exact h1 hd

/-- An orbit crosses a transversal arc at arbitrarily late times near each point of its
`ω₊`-limit set on the arc. -/
theorem omega_cross (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ} {s : ℝ → Fin 2 → ℝ}
    (harc : IsTransversalArc f M J s) {x : Fin 2 → ℝ} {u₀ : ℝ} (hu₀ : u₀ ∈ J)
    (hz : s u₀ ∈ omegaLimitSet f M true x) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ t, T ≤ t ∧ t ∈ lifetime f M x ∧ flow f M t x ∈ s '' J ∧
      dist (flow f M t x) (s u₀) < ε := by
  obtain ⟨δ, hδ, h⟩ := cross_near hM hf harc hu₀ (lt_min hε one_pos)
  obtain ⟨t1, hT1, ht1L, ht1⟩ := (omega_true_iff.mp hz).2 δ hδ (T + 1)
  obtain ⟨τ, hτ, hτL, hτJ, hτd⟩ := h _ ht1
  have hτ1 : |τ| < 1 := hτ.trans_le (min_le_right _ _)
  have hL : τ + t1 ∈ lifetime f M x := (mem_lifetime_flow hM hf ht1L).mp hτL
  refine ⟨τ + t1, ?_, hL, ?_, ?_⟩
  · have := neg_abs_le τ; linarith
  · rw [← flow_flow hM hf ht1L hL]; exact hτJ
  · rw [← flow_flow hM hf ht1L hL]; exact hτd.trans_le (min_le_left _ _)

variable {Ω : Set (Fin 2 → ℝ)}

/-- Abstract form of the argument in Lemma 7.13 / Theorem 7.16: a regular point of `ω₊(y)`
for `y ∈ Ω` forces `y` to be periodic. -/
theorem periodic_of_limit (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (hΩM : Ω ⊆ M)
    (hΩc : IsCompact Ω) (hinv : ∀ y ∈ Ω, orbit f M y ⊆ Ω)
    (H : ∀ (J : Set ℝ) (s : ℝ → Fin 2 → ℝ), IsTransversalArc f M J s → (Ω ∩ s '' J).Subsingleton)
    {y : Fin 2 → ℝ} (hy : y ∈ Ω) {z : Fin 2 → ℝ} (hz : z ∈ omegaLimitSet f M true y)
    (hfz : f z ≠ 0) : IsPeriodicPoint f M y := by
  have hyM := hΩM hy
  have hmem : ∀ t ∈ lifetime f M y, flow f M t y ∈ Ω := fun t ht => hinv y hy ⟨t, ht, rfl⟩
  have hzΩ : z ∈ Ω := (omega_true_sub hM hf hyM hΩc hΩM fun t ht _ => hmem t ht).2 hz
  obtain ⟨J, s, harc, u₀, hu₀, rfl⟩ := exists_arc hM hf (hΩM hzΩ) hfz
  obtain ⟨t1, -, ht1L, ht1J, -⟩ := omega_cross hM hf harc hu₀ hz one_pos 0
  obtain ⟨t2, ht2, ht2L, ht2J, -⟩ := omega_cross hM hf harc hu₀ hz one_pos (t1 + 1)
  have e1 : flow f M t1 y = s u₀ :=
    H J s harc ⟨hmem t1 ht1L, ht1J⟩ ⟨hzΩ, mem_image_of_mem s hu₀⟩
  have e2 : flow f M t2 y = s u₀ :=
    H J s harc ⟨hmem t2 ht2L, ht2J⟩ ⟨hzΩ, mem_image_of_mem s hu₀⟩
  exact periodic_of_eq hM hf ht1L ht2L (by linarith) (e1.trans e2.symm)

/-- Abstract form of Theorem 7.16 (iii): the `ω₊`-limit set of a non-periodic `y ∈ Ω` is a
single fixed point of `Ω`. -/
theorem omega_true_eq_fixed (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (hΩM : Ω ⊆ M)
    (hΩc : IsCompact Ω) (hinv : ∀ y ∈ Ω, orbit f M y ⊆ Ω)
    (H : ∀ (J : Set ℝ) (s : ℝ → Fin 2 → ℝ), IsTransversalArc f M J s → (Ω ∩ s '' J).Subsingleton)
    (hfin : {y | y ∈ Ω ∧ f y = 0}.Finite) {y : Fin 2 → ℝ} (hy : y ∈ Ω)
    (hnp : ¬ IsPeriodicPoint f M y) :
    ∃ a ∈ Ω, f a = 0 ∧ omegaLimitSet f M true y = {a} := by
  set W := omegaLimitSet f M true y
  obtain ⟨hne, hsub⟩ := omega_true_sub hM hf (hΩM hy) hΩc hΩM fun t ht _ => hinv y hy ⟨t, ht, rfl⟩
  have hWc : IsCompact W :=
    hΩc.of_isClosed_subset (omega_true_isClosed hΩc.isClosed hΩM hsub) hsub
  have hconn : IsPreconnected W := omega_true_preconnected hM hf hWc
  have hfix : ∀ z ∈ W, f z = 0 := fun z hz => by
    by_contra h
    exact hnp (periodic_of_limit hM hf hΩM hΩc hinv H hy hz h)
  have hWfin : W.Finite := hfin.subset fun z hz => ⟨hsub hz, hfix z hz⟩
  obtain ⟨a, ha⟩ := hne
  exact ⟨a, hsub ha, hfix a ha,
    (finite_preconnected_subsingleton hWfin hconn).eq_singleton_of_mem ha⟩

/-- The same for the `ω₋`-limit set, by time reversal. -/
theorem omega_false_eq_fixed (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (hΩM : Ω ⊆ M)
    (hΩc : IsCompact Ω) (hinv : ∀ y ∈ Ω, orbit f M y ⊆ Ω)
    (H : ∀ (J : Set ℝ) (s : ℝ → Fin 2 → ℝ), IsTransversalArc f M J s → (Ω ∩ s '' J).Subsingleton)
    (hfin : {y | y ∈ Ω ∧ f y = 0}.Finite) {y : Fin 2 → ℝ} (hy : y ∈ Ω)
    (hnp : ¬ IsPeriodicPoint f M y) :
    ∃ a ∈ Ω, f a = 0 ∧ omegaLimitSet f M false y = {a} := by
  obtain ⟨a, ha, hfa, heq⟩ := omega_true_eq_fixed (f := fun y => -f y) hM hf.neg hΩM hΩc
    (fun y hy => by rw [orbit_neg hM hf]; exact hinv y hy)
    (fun J s h => H J s (arc_neg_iff.mp h))
    (hfin.subset fun z hz => ⟨hz.1, neg_eq_zero.mp hz.2⟩) hy
    (fun h => hnp ((periodic_neg_iff hM hf).mp h))
  refine ⟨a, ha, neg_eq_zero.mp hfa, ?_⟩
  rw [omega_false_eq hM hf]; exact heq

/-- Abstract form of Lemma 7.14: a preconnected `Ω` containing a regular periodic orbit is that
orbit. -/
theorem eq_periodic_orbit (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (hΩM : Ω ⊆ M)
    (hinv : ∀ y ∈ Ω, orbit f M y ⊆ Ω)
    (H : ∀ (J : Set ℝ) (s : ℝ → Fin 2 → ℝ), IsTransversalArc f M J s → (Ω ∩ s '' J).Subsingleton)
    (hconn : IsPreconnected Ω) {y : Fin 2 → ℝ} (hy : IsPeriodicPoint f M y) (hyreg : f y ≠ 0)
    (hsub : orbit f M y ⊆ Ω) : Ω = orbit f M y := by
  set O := orbit f M y
  have hOc : IsClosed O := (isCompact_orbit_of_periodic hM hf hy).isClosed
  have hyM : y ∈ M := by obtain ⟨T, -, hT, -⟩ := hy; exact mem_of_mem_lifetime hT
  have hyO : y ∈ O := mem_orbit_self hM hf hyM
  refine Subset.antisymm ?_ hsub
  by_contra hns
  obtain ⟨z0, hz0Ω, hz0O⟩ := not_subset.mp hns
  have key : ∃ p ∈ O, ∀ δ > 0, ∃ z ∈ Ω, z ∉ O ∧ dist z p < δ := by
    by_contra hk
    push Not at hk
    choose! δ hδ hδz using hk
    set U := ⋃ p ∈ O, ball p (δ p)
    have hU : IsOpen U := isOpen_biUnion fun p _ => isOpen_ball
    obtain ⟨z, hzΩ, hzU, hzV⟩ := hconn U Oᶜ hU hOc.isOpen_compl
      (fun z _ => by
        by_cases hzO : z ∈ O
        · left; exact mem_biUnion hzO (mem_ball_self (hδ z hzO))
        · right; exact hzO)
      ⟨y, hsub hyO, mem_biUnion hyO (mem_ball_self (hδ y hyO))⟩ ⟨z0, hz0Ω, hz0O⟩
    obtain ⟨p, hpO, hzp⟩ := mem_iUnion₂.mp hzU
    exact absurd (hδz p hpO z hzΩ hzV) (not_le.mpr hzp)
  obtain ⟨p, hpO, hp⟩ := key
  have hpM : p ∈ M := orbit_subset_M hM hf y hpO
  have hfp : f p ≠ 0 := by
    obtain ⟨t, ht, rfl⟩ := hpO; exact regular_flow hM hf ht hyreg
  obtain ⟨J, s, harc, u₀, hu₀, rfl⟩ := exists_arc hM hf hpM hfp
  obtain ⟨δ, hδ, hcr⟩ := cross_near hM hf harc hu₀ one_pos
  obtain ⟨z, hzΩ, hzO, hzd⟩ := hp δ hδ
  obtain ⟨τ, -, hτL, hτJ, -⟩ := hcr z hzd
  have hzM := hΩM hzΩ
  have hfz : flow f M τ z ∈ Ω := hinv z hzΩ ⟨τ, hτL, rfl⟩
  have heq : flow f M τ z = s u₀ := H J s harc ⟨hfz, hτJ⟩ ⟨hsub hpO, mem_image_of_mem s hu₀⟩
  apply hzO
  have h1 : s u₀ ∈ orbit f M z := ⟨τ, hτL, heq⟩
  have h2 : orbit f M (s u₀) = O := orbit_eq_of_mem hM hf hpO
  rw [← h2, orbit_eq_of_mem hM hf h1]
  exact mem_orbit_self hM hf hzM

end planar

end PBF


/-! The Jordan curve theorem for a closed curve made of two arcs `A, B : [0,1] → ℝ²` with common
endpoints, stated in `Fin 2 → ℝ`: the complement of the curve is the union of two disjoint open
sets, each of whose closures contains the whole curve. -/

open Set Filter Topology Metric Function

namespace PBF


lemma sphere_sq (z : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1) : (z : (EuclideanSpace ℝ (Fin 2))) 0 ^ 2 + (z : (EuclideanSpace ℝ (Fin 2))) 1 ^ 2 = 1 := by
  have h := z.2
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two] at h
  have h2 : ‖(z : (EuclideanSpace ℝ (Fin 2))) 0‖ ^ 2 + ‖(z : (EuclideanSpace ℝ (Fin 2))) 1‖ ^ 2 = 1 := by
    have hnn : 0 ≤ ‖(z : (EuclideanSpace ℝ (Fin 2))) 0‖ ^ 2 + ‖(z : (EuclideanSpace ℝ (Fin 2))) 1‖ ^ 2 := by positivity
    have := Real.sq_sqrt hnn
    rw [h] at this
    linarith
  simpa [Real.norm_eq_abs, sq_abs] using h2

lemma sphere_param (z : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1) : (1 - (z : (EuclideanSpace ℝ (Fin 2))) 0) / 2 ∈ Icc (0 : ℝ) 1 := by
  have h := sphere_sq z
  have h0 : (z : (EuclideanSpace ℝ (Fin 2))) 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg ((z : (EuclideanSpace ℝ (Fin 2))) 1)]
  have h1 : |(z : (EuclideanSpace ℝ (Fin 2))) 0| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; exact h0
  rw [abs_le] at h1
  constructor <;> linarith [h1.1, h1.2]

lemma sphere_ext {z w : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1} (h0 : (z : (EuclideanSpace ℝ (Fin 2))) 0 = (w : (EuclideanSpace ℝ (Fin 2))) 0)
    (h1 : (z : (EuclideanSpace ℝ (Fin 2))) 1 = (w : (EuclideanSpace ℝ (Fin 2))) 1) : z = w := by
  apply Subtype.ext
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- A point of the unit circle with prescribed coordinates. -/
lemma exists_sphere (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ z : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1, (z : (EuclideanSpace ℝ (Fin 2))) 0 = a ∧ (z : (EuclideanSpace ℝ (Fin 2))) 1 = b := by
  refine ⟨⟨WithLp.toLp 2 ![a, b], ?_⟩, by simp, by simp⟩
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs, h]

theorem jordan_arcs (A B : ℝ → Fin 2 → ℝ) (hA : ContinuousOn A (Icc 0 1))
    (hB : ContinuousOn B (Icc 0 1)) (hAi : InjOn A (Icc 0 1)) (hBi : InjOn B (Icc 0 1))
    (h0 : A 0 = B 0) (h1 : A 1 = B 1)
    (hAB : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, A x = B y → x = 0 ∨ x = 1) :
    ∃ D E : Set (Fin 2 → ℝ), IsOpen D ∧ IsOpen E ∧ Disjoint D E ∧
      D ∪ E = (A '' Icc 0 1 ∪ B '' Icc 0 1)ᶜ ∧
      A '' Icc 0 1 ∪ B '' Icc 0 1 ⊆ closure D ∧ A '' Icc 0 1 ∪ B '' Icc 0 1 ⊆ closure E := by
  classical
  set Γ := A '' Icc 0 1 ∪ B '' Icc 0 1 with hΓ
  set φ : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1 → ℝ := fun z => (1 - (z : (EuclideanSpace ℝ (Fin 2))) 0) / 2 with hφ
  have hφc : Continuous φ := by
    simp only [hφ]
    have : Continuous fun z : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1 => (z : (EuclideanSpace ℝ (Fin 2))) 0 :=
      (EuclideanSpace.proj (0 : Fin 2)).continuous.comp continuous_subtype_val
    fun_prop
  have hφm : ∀ z, φ z ∈ Icc (0 : ℝ) 1 := sphere_param
  set g : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1 → Fin 2 → ℝ := fun z =>
    if (0 : ℝ) ≤ (z : (EuclideanSpace ℝ (Fin 2))) 1 then A (φ z) else B (φ z) with hg
  have hz1c : Continuous fun z : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1 => (z : (EuclideanSpace ℝ (Fin 2))) 1 :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous.comp continuous_subtype_val
  -- coordinate facts
  have hend : ∀ z : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1, (z : (EuclideanSpace ℝ (Fin 2))) 1 = 0 → φ z = 0 ∨ φ z = 1 := by
    intro z hz
    have h := sphere_sq z
    rw [hz] at h
    have : (z : (EuclideanSpace ℝ (Fin 2))) 0 = 1 ∨ (z : (EuclideanSpace ℝ (Fin 2))) 0 = -1 := by
      have : ((z : (EuclideanSpace ℝ (Fin 2))) 0 - 1) * ((z : (EuclideanSpace ℝ (Fin 2))) 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · right; linarith
    rcases this with h' | h'
    · left; simp only [hφ, h']; norm_num
    · right; simp only [hφ, h']; norm_num
  have hgc : Continuous g := by
    apply continuous_if_le continuous_const hz1c
    · exact (hA.comp_continuous hφc hφm).continuousOn
    · exact (hB.comp_continuous hφc hφm).continuousOn
    · intro z hz
      rcases hend z hz.symm with h' | h'
      · rw [h', h0]
      · rw [h', h1]
  -- recover the point from the parameter and the sign of the second coordinate
  have hrec : ∀ z w : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1, φ z = φ w → (0 ≤ (z : (EuclideanSpace ℝ (Fin 2))) 1 ↔ 0 ≤ (w : (EuclideanSpace ℝ (Fin 2))) 1) →
      z = w := by
    intro z w hzw hsg
    have e0 : (z : (EuclideanSpace ℝ (Fin 2))) 0 = (w : (EuclideanSpace ℝ (Fin 2))) 0 := by simp only [hφ] at hzw; linarith
    have hz := sphere_sq z
    have hw := sphere_sq w
    have hsq : (z : (EuclideanSpace ℝ (Fin 2))) 1 ^ 2 = (w : (EuclideanSpace ℝ (Fin 2))) 1 ^ 2 := by rw [e0] at hz; linarith
    refine sphere_ext e0 ?_
    by_cases hz0 : 0 ≤ (z : (EuclideanSpace ℝ (Fin 2))) 1
    · have hw0 := hsg.mp hz0
      exact (pow_left_inj₀ hz0 hw0 two_ne_zero).mp hsq
    · have hw0 : ¬ 0 ≤ (w : (EuclideanSpace ℝ (Fin 2))) 1 := fun h => hz0 (hsg.mpr h)
      push Not at hz0 hw0
      have := (pow_left_inj₀ (neg_nonneg.mpr hz0.le) (neg_nonneg.mpr hw0.le) two_ne_zero).mp
        (by rw [neg_sq, neg_sq]; exact hsq)
      linarith
  have hφ0 : ∀ z : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1, φ z = 0 → (z : (EuclideanSpace ℝ (Fin 2))) 1 = 0 := by
    intro z hz
    have h := sphere_sq z
    have : (z : (EuclideanSpace ℝ (Fin 2))) 0 = 1 := by simp only [hφ] at hz; linarith
    rw [this] at h
    nlinarith
  have hφ1 : ∀ z : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1, φ z = 1 → (z : (EuclideanSpace ℝ (Fin 2))) 1 = 0 := by
    intro z hz
    have h := sphere_sq z
    have : (z : (EuclideanSpace ℝ (Fin 2))) 0 = -1 := by simp only [hφ] at hz; linarith
    rw [this] at h
    nlinarith
  have hgi : Injective g := by
    intro z w hzw
    by_cases hz : 0 ≤ (z : (EuclideanSpace ℝ (Fin 2))) 1 <;> by_cases hw : 0 ≤ (w : (EuclideanSpace ℝ (Fin 2))) 1
    · simp only [hg, if_pos hz, if_pos hw] at hzw
      exact hrec z w (hAi (hφm z) (hφm w) hzw) ⟨fun _ => hw, fun _ => hz⟩
    · exfalso
      simp only [hg, if_pos hz, if_neg hw] at hzw
      push Not at hw
      rcases hAB _ (hφm z) _ (hφm w) hzw with h' | h'
      · rw [h', h0] at hzw
        have := hBi (hφm w) ⟨le_rfl, zero_le_one⟩ hzw.symm
        linarith [hφ0 w this]
      · rw [h', h1] at hzw
        have := hBi (hφm w) ⟨zero_le_one, le_rfl⟩ hzw.symm
        linarith [hφ1 w this]
    · exfalso
      simp only [hg, if_neg hz, if_pos hw] at hzw
      push Not at hz
      rcases hAB _ (hφm w) _ (hφm z) hzw.symm with h' | h'
      · rw [h', h0] at hzw
        have := hBi (hφm z) ⟨le_rfl, zero_le_one⟩ hzw
        linarith [hφ0 z this]
      · rw [h', h1] at hzw
        have := hBi (hφm z) ⟨zero_le_one, le_rfl⟩ hzw
        linarith [hφ1 z this]
    · simp only [hg, if_neg hz, if_neg hw] at hzw
      exact hrec z w (hBi (hφm z) (hφm w) hzw) ⟨fun h => absurd h hz, fun h => absurd h hw⟩
  -- the range of `g` is the curve
  have hrange : range g = Γ := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      by_cases hz : 0 ≤ (z : (EuclideanSpace ℝ (Fin 2))) 1
      · left; exact ⟨φ z, hφm z, by simp only [hg, if_pos hz]⟩
      · right; exact ⟨φ z, hφm z, by simp only [hg, if_neg hz]⟩
    · rintro (⟨θ, hθ, rfl⟩ | ⟨θ, hθ, rfl⟩)
      · have hsq : (1 - 2 * θ) ^ 2 + (√(1 - (1 - 2 * θ) ^ 2)) ^ 2 = 1 := by
          rw [Real.sq_sqrt (by nlinarith [hθ.1, hθ.2])]; ring
        obtain ⟨z, hz0, hz1⟩ := exists_sphere _ _ hsq
        have hpos : 0 ≤ (z : (EuclideanSpace ℝ (Fin 2))) 1 := by rw [hz1]; exact Real.sqrt_nonneg _
        refine ⟨z, ?_⟩
        simp only [hg, if_pos hpos, hφ, hz0]
        congr 1; ring
      · have hsq : (1 - 2 * θ) ^ 2 + (-√(1 - (1 - 2 * θ) ^ 2)) ^ 2 = 1 := by
          rw [neg_sq, Real.sq_sqrt (by nlinarith [hθ.1, hθ.2])]; ring
        obtain ⟨z, hz0, hz1⟩ := exists_sphere _ _ hsq
        have hφz : φ z = θ := by simp only [hφ, hz0]; ring
        refine ⟨z, ?_⟩
        by_cases hpos : 0 ≤ (z : (EuclideanSpace ℝ (Fin 2))) 1
        · simp only [hg, if_pos hpos, hφz]
          have hz10 : (z : (EuclideanSpace ℝ (Fin 2))) 1 = 0 := by
            have : (z : (EuclideanSpace ℝ (Fin 2))) 1 ≤ 0 := by rw [hz1]; exact neg_nonpos.mpr (Real.sqrt_nonneg _)
            linarith
          rcases hend z hz10 with h' | h'
          · rw [hφz] at h'; rw [h', h0]
          · rw [hφz] at h'; rw [h', h1]
        · simp only [hg, if_neg hpos, hφz]
  -- apply the Jordan curve theorem in the Euclidean plane
  set e := EuclideanSpace.equiv (Fin 2) ℝ with he
  set γ : sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1 → (EuclideanSpace ℝ (Fin 2)) := fun z => e.symm (g z) with hγ
  have hγc : Continuous γ := e.symm.continuous.comp hgc
  have hγi : Injective γ := e.symm.injective.comp hgi
  obtain ⟨I, O, hIo, hOo, -, -, -, -, hIO, hun, hfI, hfO⟩ :=
    JordanCurve.jordan_curve_theorem γ hγc hγi
  have hmemΓ : ∀ x, x ∈ Γ ↔ e.symm x ∈ range γ := by
    intro x
    rw [← hrange]
    constructor
    · rintro ⟨z, rfl⟩; exact ⟨z, rfl⟩
    · rintro ⟨z, hz⟩; exact ⟨z, e.symm.injective hz⟩
  have hcl : ∀ Z : Set (EuclideanSpace ℝ (Fin 2)), frontier Z = range γ → Γ ⊆ closure (e.symm ⁻¹' Z) := by
    intro Z hZ x hx
    rw [show (⇑e.symm ⁻¹' Z) = e.symm.toHomeomorph ⁻¹' Z from rfl, ← Homeomorph.preimage_closure]
    have : e.symm x ∈ frontier Z := by rw [hZ]; exact (hmemΓ x).mp hx
    exact frontier_subset_closure this
  refine ⟨e.symm ⁻¹' I, e.symm ⁻¹' O, hIo.preimage e.symm.continuous,
    hOo.preimage e.symm.continuous, hIO.preimage _, ?_, hcl I hfI, hcl O hfO⟩
  ext x
  simp only [mem_union, mem_preimage, mem_compl_iff]
  rw [hmemΓ x, ← mem_union, hun]
  rfl

end PBF


/-! Tools for Lemma 7.9: periods from coinciding orbit points, a uniform no-return time near a
compact piece of a transversal arc, and reversal of the orientation of an arc. -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

section periods

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {M : Set (Fin n → ℝ)}

lemma flow_back (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {t : ℝ}
    (ht : t ∈ lifetime f M x) :
    -t ∈ lifetime f M (flow f M t x) ∧ flow f M (-t) (flow f M t x) = x := by
  have h0 : (0 : ℝ) ∈ lifetime f M x := zero_mem_lifetime_of_mem ht
  have h1 : -t + t ∈ lifetime f M x := by rw [neg_add_cancel]; exact h0
  refine ⟨(mem_lifetime_flow hM hf ht).mpr h1, ?_⟩
  rw [flow_flow hM hf ht h1, neg_add_cancel, flow_zero hM hf h0]

/-- If `Φ(a, x) = Φ(b, x)` with `a < b`, then `b - a` is a period of `x`. -/
lemma period_of_eq (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {a b : ℝ}
    (ha : a ∈ lifetime f M x) (hb : b ∈ lifetime f M x)
    (heq : flow f M a x = flow f M b x) :
    b - a ∈ lifetime f M x ∧ flow f M (b - a) x = x := by
  have h0 : (0 : ℝ) ∈ lifetime f M x := zero_mem_lifetime_of_mem ha
  have hT : b - a ∈ lifetime f M x := by
    have h1 : -a ∈ lifetime f M (flow f M b x) := by
      rw [← heq]; exact (mem_lifetime_flow hM hf ha).mpr (by simpa using h0)
    have := (mem_lifetime_flow hM hf hb).mp h1
    simpa [sub_eq_neg_add, add_comm] using this
  refine ⟨hT, ?_⟩
  have e1 : flow f M (-a) (flow f M b x) = flow f M (b - a) x := by
    rw [flow_flow hM hf hb (by simpa [sub_eq_neg_add, add_comm] using hT)]
    ring_nf
  have e2 : flow f M (-a) (flow f M a x) = x := (flow_back hM hf ha).2
  rw [← e1, ← heq, e2]

/-- Shifting by a period. -/
lemma flow_add_period (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {P : ℝ}
    (hP : P ∈ lifetime f M x) (hPx : flow f M P x = x) {t : ℝ} (ht : t ∈ lifetime f M x) :
    t + P ∈ lifetime f M x ∧ flow f M (t + P) x = flow f M t x := by
  have h1 : t ∈ lifetime f M (flow f M P x) := by rw [hPx]; exact ht
  have h2 := (mem_lifetime_flow hM hf hP).mp h1
  refine ⟨h2, ?_⟩
  rw [← flow_flow hM hf hP h2, hPx]

lemma flow_sub_period (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin n → ℝ} {P : ℝ}
    (hP : P ∈ lifetime f M x) (hPx : flow f M P x = x) {t : ℝ} (ht : t ∈ lifetime f M x) :
    t - P ∈ lifetime f M x ∧ flow f M (t - P) x = flow f M t x := by
  have h1 : t - P + P ∈ lifetime f M x := by rw [sub_add_cancel]; exact ht
  have h2 : t - P ∈ lifetime f M (flow f M P x) := (mem_lifetime_flow hM hf hP).mpr h1
  rw [hPx] at h2
  refine ⟨h2, ?_⟩
  have := (flow_add_period hM hf hP hPx h2).2
  rw [sub_add_cancel] at this
  exact this.symm

end periods

section arcs

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

/-- Uniform no-return: near a compact piece `s([m, m'])` of a transversal arc, orbits starting on
the piece are defined for times `|τ| ≤ δ` and do not meet the arc again for `0 < |τ| ≤ δ`. -/
theorem unr (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ} {s : ℝ → Fin 2 → ℝ}
    (harc : IsTransversalArc f M J s) {m m' : ℝ} (hK : Icc m m' ⊆ J) :
    ∃ δ > 0, ∀ w ∈ Icc m m', ∀ τ, |τ| ≤ δ →
      τ ∈ lifetime f M (s w) ∧ (τ ≠ 0 → flow f M τ (s w) ∉ s '' J) := by
  have hP : ∀ w0 ∈ Icc m m', ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), w0), z.2 ∈ J →
      z.1 ∈ lifetime f M (s z.2) ∧ (z.1 ≠ 0 → flow f M z.1 (s z.2) ∉ s '' J) := by
    intro w0 hw0
    have hw0J := hK hw0
    let C := (exists_arcChart hM hf harc hw0J).some
    obtain ⟨δ, hδ, ρ', hρ', hρρ, h⟩ := C.cross hM hf
    have hsc : ContinuousAt s w0 :=
      harc.2.2.2.1.continuousOn.continuousAt (harc.1.mem_nhds hw0J)
    have h1 : ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), w0), |z.1| < δ := by
      have hc : ContinuousAt (fun z : ℝ × ℝ => |z.1|) ((0 : ℝ), w0) := by fun_prop
      exact hc.eventually (gt_mem_nhds (by simpa using hδ))
    have h2 : ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), w0), s z.2 ∈ ball (s w0) ρ' := by
      have hc : ContinuousAt (fun z : ℝ × ℝ => s z.2) ((0 : ℝ), w0) :=
        ContinuousAt.comp (g := s) (f := Prod.snd) hsc continuousAt_snd
      exact hc.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ'))
    filter_upwards [h1, h2] with z hz1 hz2 hzJ
    obtain ⟨hL, hball, hmono, -, -⟩ := h _ hz2
    have hzI : z.1 ∈ Icc (-δ) δ := by
      rw [abs_lt] at hz1; exact ⟨hz1.1.le, hz1.2.le⟩
    refine ⟨hL hzI, fun hne hmem => ?_⟩
    have hS0 : C.S (s z.2) = 0 :=
      (C.zero_iff _ (ball_subset_ball hρρ hz2)).mp ⟨z.2, hzJ, rfl⟩
    have hSt : C.S (flow f M z.1 (s z.2)) = 0 := (C.zero_iff _ (hball _ hzI)).mp hmem
    have h0I : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
    have hf0 : flow f M 0 (s z.2) = s z.2 := flow_zero' hM hf (arc_mem harc hzJ)
    have := hmono.injOn hzI h0I (by show C.S (flow f M z.1 (s z.2)) = C.S (flow f M 0 (s z.2)); rw [hSt, hf0, hS0])
    exact hne this
  obtain ⟨δ0, hδ0, hball⟩ :=
    Metric.eventually_nhds_iff.mp (isCompact_Icc.eventually_forall_of_forall_eventually
      (P := fun τ w => w ∈ J → τ ∈ lifetime f M (s w) ∧ (τ ≠ 0 → flow f M τ (s w) ∉ s '' J)) hP)
  refine ⟨δ0 / 2, by positivity, fun w hw τ hτ => hball ?_ w hw (hK hw)⟩
  rw [Real.dist_eq, sub_zero]
  linarith

/-- Reversing the orientation of a transversal arc. -/
lemma arc_rev {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} (harc : IsTransversalArc f M J s) :
    IsTransversalArc f M (Neg.neg ⁻¹' J) (fun u => s (-u)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := harc
  refine ⟨h1.preimage continuous_neg, ⟨fun a ha b hb x hx => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact h2.out hb ha ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
  · obtain ⟨t, ht⟩ := h3
    exact ⟨-t, by simpa using ht⟩
  · exact h4.comp contDiff_neg.contDiffOn (fun x hx => hx)
  · set r : (Neg.neg ⁻¹' J : Set ℝ) → J := fun t => ⟨-t.1, t.2⟩ with hr
    have hval : (Subtype.val ∘ r) = Neg.neg ∘ (Subtype.val : (Neg.neg ⁻¹' J : Set ℝ) → ℝ) := rfl
    have hre : Topology.IsEmbedding r := by
      rw [← Topology.IsEmbedding.subtypeVal.of_comp_iff, hval]
      exact (Homeomorph.neg ℝ).isEmbedding.comp Topology.IsEmbedding.subtypeVal
    exact h5.comp hre
  · intro t ht; exact h6 _ ht
  · intro t ht
    have hJ : -t ∈ J := ht
    rw [deriv_comp_neg]
    refine ⟨neg_ne_zero.mpr (h7 _ hJ).1, ?_⟩
    have hne := (h7 _ hJ).2
    have heq : (-deriv s (-t)) 0 * f (s (-t)) 1 - (-deriv s (-t)) 1 * f (s (-t)) 0 =
        -(deriv s (-t) 0 * f (s (-t)) 1 - deriv s (-t) 1 * f (s (-t)) 0) := by
      simp only [Pi.neg_apply]; ring
    rw [heq]; exact neg_ne_zero.mpr hne

end arcs

end PBF


/-! The heart of Lemma 7.9. Three consecutive intersections `y = s(v₀)`, `Φ(t₁, y) = s(v₁)`,
`Φ(t₂, y) = s(v₂)` of an orbit with a compact piece `K = s([m, m'])` of a transversal arc, with
`v₀ < v₁`, satisfy `v₁ < v₂`. The orbit piece from `y` to `s(v₁)` together with the arc piece
`s([v₀, v₁])` is a Jordan curve; the flow tubes leaving the arc piece forward and arriving
backward lie in different components, the orbit after `t₁` starts in the forward one and cannot
leave it, and it would have to arrive from the backward one if `v₂ < v₁`. -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

theorem core (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ} {s : ℝ → Fin 2 → ℝ}
    (harc : IsTransversalArc f M J s) {m m' : ℝ} (hK : Icc m m' ⊆ J) {v0 v1 v2 t1 t2 : ℝ}
    (hv0 : v0 ∈ Icc m m') (hv1 : v1 ∈ Icc m m') (hv2 : v2 ∈ Icc m m') (hlt : v0 < v1)
    (ht1 : 0 < t1) (ht12 : t1 < t2) (ht2 : t2 ∈ lifetime f M (s v0))
    (hx1 : flow f M t1 (s v0) = s v1) (hx2 : flow f M t2 (s v0) = s v2)
    (hno : ∀ t, 0 < t → t < t2 → t ≠ t1 → flow f M t (s v0) ∉ s '' Icc m m') : v1 < v2 := by
  set y := s v0 with hy
  have hyM : y ∈ M := arc_mem harc (hK hv0)
  have h0L : (0 : ℝ) ∈ lifetime f M y := zero_mem_lifetime hM hf hyM
  have hL : ∀ t, 0 ≤ t → t ≤ t2 → t ∈ lifetime f M y := fun t h1 h2 =>
    (ordConnected_lifetime y).out h0L ht2 ⟨h1, h2⟩
  have ht1L : t1 ∈ lifetime f M y := hL t1 ht1.le ht12.le
  have hinj := arc_injOn harc
  have hsK : ∀ v ∈ Icc m m', s v ∈ s '' Icc m m' := fun v hv => ⟨v, hv, rfl⟩
  have hIK : ∀ v ∈ Icc v0 v1, v ∈ Icc m m' := fun v hv =>
    ⟨by linarith [hv0.1, hv.1], by linarith [hv1.2, hv.2]⟩
  -- `y` has no period in `(0, t₂)`
  have hnoper : ∀ P, 0 < P → P < t2 → flow f M P y ≠ y := by
    intro P hP0 hP2 hPy
    by_cases hP1 : P = t1
    · rw [hP1, hx1] at hPy
      exact absurd (hinj (hK hv1) (hK hv0) hPy) (ne_of_gt hlt)
    · exact hno P hP0 hP2 hP1 (by rw [hPy]; exact hsK v0 hv0)
  obtain ⟨δ0, hδ0, hU⟩ := unr hM hf harc hK
  set δ := min δ0 ((t2 - t1) / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ0 (by linarith)
  have hδ0' : δ ≤ δ0 := min_le_left _ _
  have hδ2 : δ ≤ (t2 - t1) / 2 := min_le_right _ _
  -- short orbit pieces from points of `K` meet the orbit piece `Φ([0, t₁], y)` only at its ends
  have hClB : ∀ w ∈ Icc m m', ∀ τ, τ ≠ 0 → |τ| ≤ δ → ∀ t' ∈ Icc 0 t1,
      flow f M τ (s w) = flow f M t' y → (w = v0 ∧ 0 < τ) ∨ (w = v1 ∧ τ < 0) := by
    intro w hw τ hτ0 hτ t' ht' heq
    have hτL : τ ∈ lifetime f M (s w) := (hU w hw τ (hτ.trans hδ0')).1
    have ht'L : t' ∈ lifetime f M y := hL t' ht'.1 (by linarith [ht'.2])
    have hback := flow_back hM hf hτL
    rw [heq] at hback
    have hL'' : -τ + t' ∈ lifetime f M y := (mem_lifetime_flow hM hf ht'L).mp hback.1
    have hsw : s w = flow f M (-τ + t') y := by rw [← hback.2, flow_flow hM hf ht'L hL'']
    have hτb := abs_le.mp hτ
    rcases lt_trichotomy (-τ + t') 0 with hneg | hzero | hpos
    · exfalso
      have : |-τ + t'| ≤ δ0 := by rw [abs_le]; constructor <;> linarith [ht'.1]
      exact (hU v0 hv0 (-τ + t') this).2 (ne_of_lt hneg) (by rw [← hsw]; exact ⟨w, hK hw, rfl⟩)
    · left
      rw [hzero, flow_zero hM hf h0L] at hsw
      refine ⟨hinj (hK hw) (hK hv0) hsw, ?_⟩
      rcases lt_or_gt_of_ne hτ0 with h | h
      · linarith [ht'.1]
      · exact h
    · rcases lt_trichotomy (-τ + t') t1 with hlt1 | heq1 | hgt1
      · exfalso
        exact hno _ hpos (by linarith) (ne_of_lt hlt1) (by rw [← hsw]; exact hsK w hw)
      · right
        rw [heq1, hx1] at hsw
        refine ⟨hinj (hK hw) (hK hv1) hsw, ?_⟩
        rcases lt_or_gt_of_ne hτ0 with h | h
        · exact h
        · linarith [ht'.2]
      · exfalso
        exact hno _ hpos (by linarith [ht'.2]) (ne_of_gt hgt1) (by rw [← hsw]; exact hsK w hw)
  -- short orbit pieces from points of `K` do not meet the arc piece
  have hClA : ∀ w ∈ Icc m m', ∀ τ, τ ≠ 0 → |τ| ≤ δ → ∀ v ∈ Icc v0 v1,
      flow f M τ (s w) ≠ s v := by
    intro w hw τ hτ0 hτ v hv heq
    exact (hU w hw τ (hτ.trans hδ0')).2 hτ0 (by rw [heq]; exact ⟨v, hK (hIK v hv), rfl⟩)
  -- the Jordan curve
  set A : ℝ → Fin 2 → ℝ := fun θ => flow f M (θ * t1) y with hAdef
  set B : ℝ → Fin 2 → ℝ := fun θ => s (v0 + θ * (v1 - v0)) with hBdef
  have hAL : ∀ θ ∈ Icc (0 : ℝ) 1, θ * t1 ∈ Icc 0 t1 := fun θ hθ =>
    ⟨mul_nonneg hθ.1 ht1.le, by nlinarith [hθ.2]⟩
  have hBI : ∀ θ ∈ Icc (0 : ℝ) 1, v0 + θ * (v1 - v0) ∈ Icc v0 v1 := fun θ hθ =>
    ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩
  have hΓ : ∀ z ∈ A '' Icc 0 1 ∪ B '' Icc 0 1,
      (∃ t' ∈ Icc 0 t1, flow f M t' y = z) ∨ (∃ v ∈ Icc v0 v1, s v = z) := by
    rintro z (⟨θ, hθ, rfl⟩ | ⟨θ, hθ, rfl⟩)
    · exact Or.inl ⟨θ * t1, hAL θ hθ, rfl⟩
    · exact Or.inr ⟨_, hBI θ hθ, rfl⟩
  have hBmem : ∀ v ∈ Icc v0 v1, s v ∈ A '' Icc 0 1 ∪ B '' Icc 0 1 := by
    intro v hv
    right
    refine ⟨(v - v0) / (v1 - v0), ⟨div_nonneg (by linarith [hv.1]) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith [hv.2])⟩, ?_⟩
    simp only [hBdef]
    congr 1
    rw [div_mul_cancel₀ _ (by linarith : v1 - v0 ≠ 0)]; ring
  have hAc : ContinuousOn A (Icc 0 1) := by
    intro θ hθ
    have hθL := hL _ (hAL θ hθ).1 ((hAL θ hθ).2.trans ht12.le)
    exact (ContinuousAt.comp (g := fun t => flow f M t y) (f := fun θ : ℝ => θ * t1) ((flow_sol hM hf y) _ hθL).2.continuousAt
      (by fun_prop : ContinuousAt (fun θ : ℝ => θ * t1) θ)).continuousWithinAt
  have hBc : ContinuousOn B (Icc 0 1) :=
    harc.2.2.2.1.continuousOn.comp (by fun_prop : Continuous fun θ : ℝ => v0 + θ * (v1 - v0)).continuousOn
      (fun θ hθ => hK (hIK _ (hBI θ hθ)))
  have hAi : InjOn A (Icc 0 1) := by
    have key : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ θ' ∈ Icc (0 : ℝ) 1, θ < θ' → A θ ≠ A θ' := by
      intro θ hθ θ' hθ' hlt' heq
      have h1 := hAL θ hθ
      have h2 := hAL θ' hθ'
      have hP := period_of_eq hM hf (hL _ h1.1 (h1.2.trans ht12.le)) (hL _ h2.1 (h2.2.trans ht12.le))
        heq
      exact hnoper _ (by nlinarith) (by nlinarith [h2.2, h1.1]) hP.2
    intro θ hθ θ' hθ' heq
    rcases lt_trichotomy θ θ' with h | h | h
    · exact absurd heq (key θ hθ θ' hθ' h)
    · exact h
    · exact absurd heq.symm (key θ' hθ' θ hθ h)
  have hBi : InjOn B (Icc 0 1) := by
    intro θ hθ θ' hθ' heq
    have := hinj (hK (hIK _ (hBI θ hθ))) (hK (hIK _ (hBI θ' hθ'))) heq
    have hne : v1 - v0 ≠ 0 := by linarith
    have : (θ - θ') * (v1 - v0) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hne
  have hA0 : A 0 = B 0 := by
    simp only [hAdef, hBdef, zero_mul, add_zero]
    exact flow_zero hM hf h0L
  have hA1 : A 1 = B 1 := by
    simp only [hAdef, hBdef, one_mul]
    rw [hx1]; congr 1; ring
  have hAB : ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, A x = B x' → x = 0 ∨ x = 1 := by
    intro x hx x' hx' heq
    by_contra hc
    push Not at hc
    have hx0 : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hc.1)
    have hx1' : x < 1 := lt_of_le_of_ne hx.2 hc.2
    exact hno (x * t1) (by positivity) (by nlinarith) (by nlinarith)
      (by rw [show flow f M (x * t1) (s v0) = A x from rfl, heq]
          exact hsK _ (hIK _ (hBI x' hx')))
  obtain ⟨D, E, hDo, hEo, hDE, hun, hcD, hcE⟩ := jordan_arcs A B hAc hBc hAi hBi hA0 hA1 hAB
  set Γ := A '' Icc 0 1 ∪ B '' Icc 0 1 with hΓdef
  have hDΓ : ∀ z ∈ D, z ∉ Γ := fun z hz hzΓ => by
    have : z ∈ D ∪ E := Or.inl hz
    rw [hun] at this; exact this hzΓ
  have hEΓ : ∀ z ∈ E, z ∉ Γ := fun z hz hzΓ => by
    have : z ∈ D ∪ E := Or.inr hz
    rw [hun] at this; exact this hzΓ
  have hside : ∀ Z : Set (Fin 2 → ℝ), IsPreconnected Z → (∀ z ∈ Z, z ∉ Γ) → Z ⊆ D ∨ Z ⊆ E :=
    fun Z hZ hZΓ => hZ.subset_or_subset hDo hEo hDE (fun z hz => by rw [hun]; exact hZΓ z hz)
  -- the flow tubes
  set F : ℝ × ℝ → Fin 2 → ℝ := fun q => flow f M q.2 (s q.1) with hFdef
  have hFc : ∀ q : ℝ × ℝ, q.1 ∈ Icc m m' → |q.2| ≤ δ → ContinuousAt F q := by
    intro q hq1 hq2
    have hqL := (hU q.1 hq1 q.2 (hq2.trans hδ0')).1
    have hc := (flow_cont hM hf hqL).2
    have hsc : ContinuousAt s q.1 :=
      harc.2.2.2.1.continuousOn.continuousAt (harc.1.mem_nhds (hK hq1))
    have hin : ContinuousAt (fun q : ℝ × ℝ => (q.2, s q.1)) q :=
      continuousAt_snd.prodMk (ContinuousAt.comp (g := s) (f := Prod.fst) hsc continuousAt_fst)
    exact ContinuousAt.comp (g := fun p : ℝ × (Fin 2 → ℝ) => flow f M p.1 p.2)
      (f := fun q : ℝ × ℝ => (q.2, s q.1)) hc hin
  set Pp := F '' (Ioc v0 v1 ×ˢ Ioo 0 δ) with hPpdef
  set Pm := F '' (Ico m v1 ×ˢ Ioo (-δ) 0) with hPmdef
  have hPpc : IsPreconnected Pp := by
    refine ((convex_Ioc v0 v1).prod (convex_Ioo 0 δ)).isPreconnected.image F ?_
    intro q hq
    refine (hFc q ⟨by linarith [hv0.1, hq.1.1], by linarith [hv1.2, hq.1.2]⟩
      (abs_le.mpr ⟨by linarith [hq.2.1], hq.2.2.le⟩)).continuousWithinAt
  have hPmc : IsPreconnected Pm := by
    refine ((convex_Ico m v1).prod (convex_Ioo (-δ) 0)).isPreconnected.image F ?_
    intro q hq
    refine (hFc q ⟨hq.1.1, by linarith [hv1.2, hq.1.2]⟩
      (abs_le.mpr ⟨hq.2.1.le, by linarith [hq.2.2]⟩)).continuousWithinAt
  have hPpΓ : ∀ z ∈ Pp, z ∉ Γ := by
    rintro z ⟨q, hq, rfl⟩ hzΓ
    have hq1 : q.1 ∈ Icc m m' := ⟨by linarith [hv0.1, hq.1.1], by linarith [hv1.2, hq.1.2]⟩
    have hq2 : |q.2| ≤ δ := abs_le.mpr ⟨by linarith [hq.2.1], hq.2.2.le⟩
    rcases hΓ _ hzΓ with ⟨t', ht', he⟩ | ⟨v, hv, he⟩
    · rcases hClB q.1 hq1 q.2 (ne_of_gt hq.2.1) hq2 t' ht' he.symm with ⟨hw, -⟩ | ⟨-, hτ⟩
      · linarith [hq.1.1]
      · linarith [hq.2.1]
    · exact hClA q.1 hq1 q.2 (ne_of_gt hq.2.1) hq2 v hv he.symm
  have hPmΓ : ∀ z ∈ Pm, z ∉ Γ := by
    rintro z ⟨q, hq, rfl⟩ hzΓ
    have hq1 : q.1 ∈ Icc m m' := ⟨hq.1.1, by linarith [hv1.2, hq.1.2]⟩
    have hq2 : |q.2| ≤ δ := abs_le.mpr ⟨hq.2.1.le, by linarith [hq.2.2]⟩
    rcases hΓ _ hzΓ with ⟨t', ht', he⟩ | ⟨v, hv, he⟩
    · rcases hClB q.1 hq1 q.2 (ne_of_lt hq.2.2) hq2 t' ht' he.symm with ⟨-, hτ⟩ | ⟨hw, -⟩
      · linarith [hq.2.2]
      · linarith [hq.1.2]
    · exact hClA q.1 hq1 q.2 (ne_of_lt hq.2.2) hq2 v hv he.symm
  -- the orbit after `t₁`
  set O := (fun t => flow f M t y) '' Ioo t1 t2 with hOdef
  have hOc : IsPreconnected O := by
    refine isPreconnected_Ioo.image _ (fun t ht => ?_)
    exact ((flow_sol hM hf y) t (hL t (by linarith [ht.1]) ht.2.le)).2.continuousAt.continuousWithinAt
  have hOΓ : ∀ z ∈ O, z ∉ Γ := by
    rintro z ⟨t, ht, rfl⟩ hzΓ
    rcases hΓ _ hzΓ with ⟨t', ht', he⟩ | ⟨v, hv, he⟩
    · have hP := period_of_eq hM hf (hL t' ht'.1 (ht'.2.trans ht12.le))
        (hL t (by linarith [ht.1]) ht.2.le) he
      exact hnoper _ (by linarith [ht'.2, ht.1]) (by linarith [ht'.1, ht.2]) hP.2
    · exact hno t (by linarith [ht.1]) ht.2 (ne_of_gt ht.1) (by have he' : s v = flow f M t y := he; rw [← he']; exact hsK v (hIK v hv))
  have hOPp : (O ∩ Pp).Nonempty := by
    have hL' : δ / 2 + t1 ∈ lifetime f M y := hL _ (by linarith) (by linarith)
    refine ⟨flow f M (δ / 2 + t1) y, ⟨δ / 2 + t1, ⟨by linarith, by linarith⟩, rfl⟩,
      ⟨(v1, δ / 2), ⟨⟨hlt, le_rfl⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩⟩
    show flow f M (δ / 2) (s v1) = _
    rw [← hx1, flow_flow hM hf ht1L hL']
  -- every component meets the tubes near the middle of the arc piece
  have hDC : ∀ Z : Set (Fin 2 → ℝ), Γ ⊆ closure Z → (∀ z ∈ Z, z ∉ Γ) →
      (Z ∩ (Pp ∪ Pm)).Nonempty := by
    intro Z hcl hZΓ
    set w := (v0 + v1) / 2 with hwdef
    have hwI : w ∈ Icc v0 v1 := ⟨by linarith, by linarith⟩
    have hwJ := hK (hIK w hwI)
    obtain ⟨ε1, hε1, hinv⟩ := arc_inv_cont harc hwJ (ε := (v1 - v0) / 2) (by linarith)
    obtain ⟨r, hr, hcn⟩ := cross_near hM hf harc hwJ (ε := min δ ε1) (lt_min hδ hε1)
    obtain ⟨z, hzZ, hzd⟩ := Metric.mem_closure_iff.mp (hcl (hBmem w hwI)) r hr
    obtain ⟨τ, hτ, hτL, ⟨w', hw'J, hw'e⟩, hd⟩ := hcn z (by rw [dist_comm]; exact hzd)
    have hw'w : |w' - w| < (v1 - v0) / 2 :=
      hinv w' hw'J (by rw [hw'e]; exact hd.trans_le (min_le_right _ _))
    obtain ⟨hw1, hw2⟩ := abs_lt.mp hw'w
    have hw'0 : v0 < w' := by linarith
    have hw'1 : w' < v1 := by linarith
    have hzback : flow f M (-τ) (s w') = z := by rw [hw'e]; exact (flow_back hM hf hτL).2
    have hτδ := abs_lt.mp (hτ.trans_le (min_le_left _ _))
    rcases lt_trichotomy τ 0 with hneg | h0 | hpos
    · exact ⟨z, hzZ, Or.inl ⟨(w', -τ), ⟨⟨hw'0, hw'1.le⟩, ⟨by linarith, by linarith⟩⟩, hzback⟩⟩
    · exfalso
      apply hZΓ z hzZ
      rw [← hzback, h0, neg_zero, flow_zero' hM hf (arc_mem harc hw'J)]
      exact hBmem w' ⟨hw'0.le, hw'1.le⟩
    · exact ⟨z, hzZ, Or.inr ⟨(w', -τ), ⟨⟨by linarith [hv0.1], hw'1⟩, ⟨by linarith, by linarith⟩⟩,
        hzback⟩⟩
  -- conclusion
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le hcon with heq | hlt2
  · have hP := period_of_eq hM hf ht1L ht2 (by rw [hx1, hx2, heq])
    exact hnoper (t2 - t1) (by linarith) (by linarith) hP.2
  · have hOPm : (O ∩ Pm).Nonempty := by
      have hL' : -(δ / 2) + t2 ∈ lifetime f M y := hL _ (by linarith) (by linarith)
      refine ⟨flow f M (-(δ / 2) + t2) y, ⟨-(δ / 2) + t2, ⟨by linarith, by linarith⟩, rfl⟩,
        ⟨(v2, -(δ / 2)), ⟨⟨hv2.1, hlt2⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩⟩
      show flow f M (-(δ / 2)) (s v2) = _
      rw [← hx2, flow_flow hM hf ht2 hL']
    have key : ∀ X Y : Set (Fin 2 → ℝ), Disjoint X Y → O ⊆ X → (Pp ⊆ X ∨ Pp ⊆ Y) →
        (Pm ⊆ X ∨ Pm ⊆ Y) → (Y ∩ (Pp ∪ Pm)).Nonempty → False := by
      intro X Y hXY hO hp hm hY
      have hpX : Pp ⊆ X := hp.resolve_right (fun h => by
        obtain ⟨z, h1, h2⟩ := hOPp; exact disjoint_left.mp hXY (hO h1) (h h2))
      have hmX : Pm ⊆ X := hm.resolve_right (fun h => by
        obtain ⟨z, h1, h2⟩ := hOPm; exact disjoint_left.mp hXY (hO h1) (h h2))
      obtain ⟨z, hzY, hz | hz⟩ := hY
      · exact disjoint_left.mp hXY (hpX hz) hzY
      · exact disjoint_left.mp hXY (hmX hz) hzY
    rcases hside O hOc hOΓ with hO | hO
    · exact key D E hDE hO (hside Pp hPpc hPpΓ) (hside Pm hPmc hPmΓ) (hDC E hcE hEΓ)
    · exact key E D hDE.symm hO (hside Pp hPpc hPpΓ).symm (hside Pm hPmc hPmΓ).symm
        (hDC D hcD hDΓ)

end PBF


/-! Lemma 7.9 for `σ = +`: from consecutive triples (the Jordan curve argument in `core`) to all
triples of intersection times, via a compact piece of the arc containing the three intersection
points (whose intersection times are uniformly separated), and then to monotonicity. -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

/-- The value `b` continues the direction from `a` to `b` towards `c`. -/
def Tri (a b c : ℝ) : Prop := (a < b ∧ b < c) ∨ (b < a ∧ c < b) ∨ (a = b ∧ b = c)

lemma tri_left {a b c d : ℝ} (h1 : Tri a b c) (h2 : Tri b c d) : Tri a c d := by
  rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

lemma tri_right {a b c d : ℝ} (h1 : Tri a b c) (h2 : Tri b c d) : Tri a b d := by
  rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-- If every triple of points of `S` satisfies `Tri`, then `u` is monotone or antitone on `S`. -/
lemma mono_or_anti {S : Set ℝ} {u : ℝ → ℝ}
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c → Tri (u a) (u b) (u c)) :
    MonotoneOn u S ∨ AntitoneOn u S := by
  -- a decreasing and an increasing pair cannot share their right end point
  have shared : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < z → y < z → u z < u x → u y < u z → False := by
    intro x hx y hy z hz hxz hyz h1 h2
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · rcases h x hx y hy z hz hxy hyz with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
    · linarith
    · rcases h y hy x hx z hz hyx hxz with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
  by_contra hc
  simp only [MonotoneOn, AntitoneOn, not_or, not_forall, not_le] at hc
  obtain ⟨⟨p, hp, q, hq, hpq, h1⟩, ⟨r, hr, w, hw, hrw, h2⟩⟩ := hc
  have hpq' : p < q := lt_of_le_of_ne hpq (by rintro rfl; exact lt_irrefl _ h1)
  have hrw' : r < w := lt_of_le_of_ne hrw (by rintro rfl; exact lt_irrefl _ h2)
  rcases lt_trichotomy q w with hqw | rfl | hwq
  · have hwq : u w < u q := by
      rcases h p hp q hq w hw hpq' hqw with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
    exact shared q hq r hr w hw hqw hrw' hwq h2
  · exact shared p hp r hr q hq hpq' hrw' h1 h2
  · have hwq' : u w < u q := by
      rcases h r hr w hw q hq hrw' hwq with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
    exact shared p hp w hw q hq hpq' hwq h1 hwq'

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

/-- Consecutive triple, increasing case. -/
lemma ct_lt (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ} {s : ℝ → Fin 2 → ℝ}
    (harc : IsTransversalArc f M J s) {m m' : ℝ} (hK : Icc m m' ⊆ J) {x : Fin 2 → ℝ}
    {p q r vp vq vr : ℝ} (hpL : p ∈ lifetime f M x) (hrL : r ∈ lifetime f M x) (hpq : p < q)
    (hqr : q < r) (hvp : vp ∈ Icc m m') (hvq : vq ∈ Icc m m') (hvr : vr ∈ Icc m m')
    (hep : flow f M p x = s vp) (heq : flow f M q x = s vq) (her : flow f M r x = s vr)
    (hlt : vp < vq) (hcons : ∀ t, p < t → t < r → t ≠ q → flow f M t x ∉ s '' Icc m m') :
    vq < vr := by
  have hL : ∀ t, p ≤ t → t ≤ r → t ∈ lifetime f M x := fun t h1 h2 =>
    (ordConnected_lifetime x).out hpL hrL ⟨h1, h2⟩
  refine core hM hf harc hK hvp hvq hvr hlt (t1 := q - p) (t2 := r - p) (by linarith)
    (by linarith) ?_ ?_ ?_ ?_
  · rw [← hep]; exact (mem_lifetime_flow hM hf hpL).mpr (by rw [sub_add_cancel]; exact hrL)
  · rw [← hep, flow_flow hM hf hpL (by rw [sub_add_cancel]; exact hL q hpq.le hqr.le),
      sub_add_cancel, heq]
  · rw [← hep, flow_flow hM hf hpL (by rw [sub_add_cancel]; exact hrL), sub_add_cancel, her]
  · intro t ht0 ht2 htq hmem
    rw [← hep] at hmem
    have hL' : t + p ∈ lifetime f M x := hL _ (by linarith) (by linarith)
    rw [flow_flow hM hf hpL hL'] at hmem
    exact hcons (t + p) (by linarith) (by linarith) (fun h => htq (by linarith)) hmem

/-- Consecutive triple, decreasing case (reverse the arc). -/
lemma ct_gt (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ} {s : ℝ → Fin 2 → ℝ}
    (harc : IsTransversalArc f M J s) {m m' : ℝ} (hK : Icc m m' ⊆ J) {x : Fin 2 → ℝ}
    {p q r vp vq vr : ℝ} (hpL : p ∈ lifetime f M x) (hrL : r ∈ lifetime f M x) (hpq : p < q)
    (hqr : q < r) (hvp : vp ∈ Icc m m') (hvq : vq ∈ Icc m m') (hvr : vr ∈ Icc m m')
    (hep : flow f M p x = s vp) (heq : flow f M q x = s vq) (her : flow f M r x = s vr)
    (hlt : vq < vp) (hcons : ∀ t, p < t → t < r → t ≠ q → flow f M t x ∉ s '' Icc m m') :
    vr < vq := by
  have hK' : Icc (-m') (-m) ⊆ Neg.neg ⁻¹' J := fun v hv =>
    hK ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have hneg : ∀ v ∈ Icc m m', -v ∈ Icc (-m') (-m) := fun v hv =>
    ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have key := ct_lt hM hf (arc_rev harc) hK' (x := x) (vp := -vp) (vq := -vq) (vr := -vr) hpL hrL
    hpq hqr (hneg vp hvp) (hneg vq hvq) (hneg vr hvr)
    (by show flow f M p x = s (- -vp); rw [neg_neg]; exact hep)
    (by show flow f M q x = s (- -vq); rw [neg_neg]; exact heq)
    (by show flow f M r x = s (- -vr); rw [neg_neg]; exact her) (by linarith)
    (fun t h1 h2 h3 hmem => by
      apply hcons t h1 h2 h3
      obtain ⟨v, hv, hve⟩ := hmem
      exact ⟨-v, ⟨by linarith [hv.2], by linarith [hv.1]⟩, hve⟩)
  linarith

/-- Consecutive triple, periodic case. -/
lemma ct_eq (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ} {s : ℝ → Fin 2 → ℝ}
    (harc : IsTransversalArc f M J s) {m m' : ℝ} (hK : Icc m m' ⊆ J) {x : Fin 2 → ℝ}
    {p q r vp vq vr : ℝ} (hpL : p ∈ lifetime f M x) (hrL : r ∈ lifetime f M x) (hpq : p < q)
    (hqr : q < r) (hvq : vq ∈ Icc m m') (hvr : vr ∈ Icc m m')
    (hep : flow f M p x = s vp) (heq : flow f M q x = s vq) (her : flow f M r x = s vr)
    (hpqv : vp = vq) (hcons : ∀ t, p < t → t < r → t ≠ q → flow f M t x ∉ s '' Icc m m') :
    vq = vr := by
  have hqL : q ∈ lifetime f M x := (ordConnected_lifetime x).out hpL hrL ⟨hpq.le, hqr.le⟩
  obtain ⟨hPL, hPx⟩ := period_of_eq hM hf hpL hqL (by rw [hep, heq, hpqv])
  obtain ⟨-, hfl⟩ := flow_sub_period hM hf hPL hPx hrL
  by_cases hrq : r - (q - p) = q
  · rw [hrq, heq, her] at hfl
    exact arc_injOn harc (hK hvq) (hK hvr) hfl
  · exfalso
    exact hcons (r - (q - p)) (by linarith) (by linarith) hrq
      (by rw [hfl, her]; exact ⟨vr, hvr, rfl⟩)

/-- Times of intersection with the compact arc piece `s([m, m'])`. -/
def Cr (f : (Fin 2 → ℝ) → Fin 2 → ℝ) (M : Set (Fin 2 → ℝ)) (s : ℝ → Fin 2 → ℝ) (m m' : ℝ)
    (x : Fin 2 → ℝ) : Set ℝ :=
  {t | t ∈ lifetime f M x ∧ 0 < t ∧ flow f M t x ∈ s '' Icc m m'}

section crossings

variable {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} {m m' δ : ℝ} {x : Fin 2 → ℝ}

/-- Intersection times with a compact arc piece are `δ`-separated. -/
lemma sep (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (hK : Icc m m' ⊆ J)
    (hU : ∀ w ∈ Icc m m', ∀ τ, |τ| ≤ δ →
      τ ∈ lifetime f M (s w) ∧ (τ ≠ 0 → flow f M τ (s w) ∉ s '' J))
    {t t' : ℝ} (ht : t ∈ lifetime f M x) (ht' : t' ∈ lifetime f M x)
    (hmt : flow f M t x ∈ s '' Icc m m') (hmt' : flow f M t' x ∈ s '' Icc m m') (hlt : t < t') :
    δ < t' - t := by
  by_contra hle
  push Not at hle
  obtain ⟨w, hw, hwe⟩ := hmt
  have h1 : t' - t + t ∈ lifetime f M x := by rw [sub_add_cancel]; exact ht'
  have h2 : flow f M (t' - t) (flow f M t x) = flow f M t' x := by
    rw [flow_flow hM hf ht h1, sub_add_cancel]
  rw [← hwe] at h2
  apply (hU w hw (t' - t) (by rw [abs_of_pos (by linarith)]; exact hle)).2 (by linarith)
  rw [h2]
  obtain ⟨w', hw', hw'e⟩ := hmt'
  exact ⟨w', hK hw', hw'e⟩

/-- The next intersection time. -/
lemma next_cross (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (harc : IsTransversalArc f M J s)
    (hK : Icc m m' ⊆ J) (hδ : 0 < δ)
    (hU : ∀ w ∈ Icc m m', ∀ τ, |τ| ≤ δ →
      τ ∈ lifetime f M (s w) ∧ (τ ≠ 0 → flow f M τ (s w) ∉ s '' J))
    {q r : ℝ} (hq : q ∈ Cr f M s m m' x) (hr : r ∈ Cr f M s m m' x) (hqr : q < r) :
    ∃ q' ∈ Cr f M s m m' x, q < q' ∧ q' ≤ r ∧ ∀ t ∈ Cr f M s m m' x, q < t → q' ≤ t := by
  set T := Icc (q + δ) r ∩ (fun t => flow f M t x) ⁻¹' (s '' Icc m m') with hT
  have hsep := sep hM hf hK hU hq.1 hr.1 hq.2.2 hr.2.2 hqr
  have hrT : r ∈ T := ⟨⟨by linarith, le_rfl⟩, hr.2.2⟩
  have hL : ∀ t, q ≤ t → t ≤ r → t ∈ lifetime f M x := fun t h1 h2 =>
    (ordConnected_lifetime x).out hq.1 hr.1 ⟨h1, h2⟩
  have hKc : IsClosed (s '' Icc m m') :=
    (isCompact_Icc.image_of_continuousOn (harc.2.2.2.1.continuousOn.mono hK)).isClosed
  have hcont : ContinuousOn (fun t => flow f M t x) (Icc (q + δ) r) := by
    intro t ht
    exact ((flow_sol hM hf x) t (hL t (by linarith [ht.1]) ht.2)).2.continuousAt.continuousWithinAt
  have hTc : IsClosed T := hcont.preimage_isClosed_of_isClosed isClosed_Icc hKc
  have hbdd : BddBelow T := ⟨q + δ, fun t ht => ht.1.1⟩
  have hmem := hTc.csInf_mem ⟨r, hrT⟩ hbdd
  refine ⟨sInf T, ⟨hL _ (by linarith [hmem.1.1]) hmem.1.2, by linarith [hmem.1.1, hq.2.1],
    hmem.2⟩, by linarith [hmem.1.1], hmem.1.2, fun t ht hqt => ?_⟩
  by_contra hlt
  push Not at hlt
  have := sep hM hf hK hU hq.1 ht.1 hq.2.2 ht.2.2 hqt
  have htT : t ∈ T := ⟨⟨by linarith, by linarith [hmem.1.2]⟩, ht.2.2⟩
  linarith [csInf_le hbdd htT]

/-- Every consecutive triple of intersection times satisfies `Tri`. -/
lemma ct (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (harc : IsTransversalArc f M J s)
    (hK : Icc m m' ⊆ J) {u : ℝ → ℝ}
    (hv : ∀ t ∈ Cr f M s m m' x, u t ∈ Icc m m' ∧ s (u t) = flow f M t x)
    {p q r : ℝ} (hp : p ∈ Cr f M s m m' x) (hq : q ∈ Cr f M s m m' x)
    (hr : r ∈ Cr f M s m m' x) (hpq : p < q) (hqr : q < r)
    (hcons : ∀ t ∈ Cr f M s m m' x, p < t → t < r → t = q) : Tri (u p) (u q) (u r) := by
  have hc : ∀ t, p < t → t < r → t ≠ q → flow f M t x ∉ s '' Icc m m' := by
    intro t h1 h2 h3 hmem
    have htL : t ∈ lifetime f M x := (ordConnected_lifetime x).out hp.1 hr.1 ⟨h1.le, h2.le⟩
    exact h3 (hcons t ⟨htL, by linarith [hp.2.1], hmem⟩ h1 h2)
  obtain ⟨hvp, hep⟩ := hv p hp
  obtain ⟨hvq, heq⟩ := hv q hq
  obtain ⟨hvr, her⟩ := hv r hr
  rcases lt_trichotomy (u p) (u q) with h | h | h
  · exact Or.inl ⟨h, ct_lt hM hf harc hK hp.1 hr.1 hpq hqr hvp hvq hvr hep.symm heq.symm her.symm
      h hc⟩
  · exact Or.inr (Or.inr ⟨h, ct_eq hM hf harc hK hp.1 hr.1 hpq hqr hvq hvr hep.symm heq.symm
      her.symm h hc⟩)
  · exact Or.inr (Or.inl ⟨h, ct_gt hM hf harc hK hp.1 hr.1 hpq hqr hvp hvq hvr hep.symm heq.symm
      her.symm h hc⟩)

/-- All triples of intersection times with a compact arc piece satisfy `Tri`. -/
lemma all_tri (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (harc : IsTransversalArc f M J s)
    (hK : Icc m m' ⊆ J) (hδ : 0 < δ)
    (hU : ∀ w ∈ Icc m m', ∀ τ, |τ| ≤ δ →
      τ ∈ lifetime f M (s w) ∧ (τ ≠ 0 → flow f M τ (s w) ∉ s '' J))
    {u : ℝ → ℝ} (hv : ∀ t ∈ Cr f M s m m' x, u t ∈ Icc m m' ∧ s (u t) = flow f M t x) :
    ∀ n : ℕ, ∀ p ∈ Cr f M s m m' x, ∀ q ∈ Cr f M s m m' x, ∀ r ∈ Cr f M s m m' x,
      p < q → q < r → r - p ≤ n * δ → Tri (u p) (u q) (u r) := by
  intro n
  induction n with
  | zero =>
    intro p hp q hq r hr hpq hqr h
    simp only [Nat.cast_zero, zero_mul] at h
    linarith
  | succ n ih =>
    intro p hp q hq r hr hpq hqr hle
    rw [Nat.cast_succ, add_mul, one_mul] at hle
    have hspq := sep hM hf hK hU hp.1 hq.1 hp.2.2 hq.2.2 hpq
    have hsqr := sep hM hf hK hU hq.1 hr.1 hq.2.2 hr.2.2 hqr
    obtain ⟨p', hp', hpp', hp'q, hp'min⟩ := next_cross hM hf harc hK hδ hU hp hq hpq
    rcases lt_or_eq_of_le hp'q with hlt | heq
    · have hspp := sep hM hf hK hU hp.1 hp'.1 hp.2.2 hp'.2.2 hpp'
      have h1 := ih p hp p' hp' q hq hpp' hlt (by linarith)
      have h2 := ih p' hp' q hq r hr hlt hqr (by linarith)
      exact tri_left h1 h2
    · subst heq
      obtain ⟨q', hq', hqq', hq'r, hq'min⟩ := next_cross hM hf harc hK hδ hU hp' hr hqr
      have hT : Tri (u p) (u p') (u q') := by
        refine ct hM hf harc hK hv hp hp' hq' hpp' hqq' (fun t ht h1 h2 => ?_)
        by_contra hne
        rcases lt_or_gt_of_ne hne with h3 | h3
        · linarith [hp'min t ht h1]
        · linarith [hq'min t ht h3]
      rcases lt_or_eq_of_le hq'r with hlt' | heq'
      · have h2 := ih p' hp' q' hq' r hr hqq' hlt' (by linarith)
        exact tri_right hT h2
      · rw [← heq']; exact hT

end crossings

/-- Lemma 7.9 for `σ = +`. -/
theorem mono_true (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin 2 → ℝ}
    {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} (harc : IsTransversalArc f M J s) (u : ℝ → ℝ)
    (hu : ∀ t, t ∈ lifetime f M x → 0 < t → flow f M t x ∈ s '' J →
      u t ∈ J ∧ s (u t) = flow f M t x) :
    MonotoneOn u {t | t ∈ lifetime f M x ∧ 0 < t ∧ flow f M t x ∈ s '' J} ∨
      AntitoneOn u {t | t ∈ lifetime f M x ∧ 0 < t ∧ flow f M t x ∈ s '' J} := by
  apply mono_or_anti
  intro a ha b hb c hc hab hbc
  obtain ⟨hua, hsa⟩ := hu a ha.1 ha.2.1 ha.2.2
  obtain ⟨hub, hsb⟩ := hu b hb.1 hb.2.1 hb.2.2
  obtain ⟨huc, hsc⟩ := hu c hc.1 hc.2.1 hc.2.2
  have hmJ : min (min (u a) (u b)) (u c) ∈ J := by
    rcases min_choice (min (u a) (u b)) (u c) with h | h
    · rw [h]
      rcases min_choice (u a) (u b) with h' | h'
      · rw [h']; exact hua
      · rw [h']; exact hub
    · rw [h]; exact huc
  have hm'J : max (max (u a) (u b)) (u c) ∈ J := by
    rcases max_choice (max (u a) (u b)) (u c) with h | h
    · rw [h]
      rcases max_choice (u a) (u b) with h' | h'
      · rw [h']; exact hua
      · rw [h']; exact hub
    · rw [h]; exact huc
  set m := min (min (u a) (u b)) (u c) with hm
  set m' := max (max (u a) (u b)) (u c) with hm'
  have hma : u a ∈ Icc m m' :=
    ⟨(min_le_left _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_left _ _)⟩
  have hmb : u b ∈ Icc m m' :=
    ⟨(min_le_left _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_left _ _)⟩
  have hmc : u c ∈ Icc m m' := ⟨min_le_right _ _, le_max_right _ _⟩
  have hK : Icc m m' ⊆ J := harc.2.1.out hmJ hm'J
  obtain ⟨δ, hδ, hU⟩ := unr hM hf harc hK
  have hv : ∀ t ∈ Cr f M s m m' x, u t ∈ Icc m m' ∧ s (u t) = flow f M t x := by
    intro t ht
    obtain ⟨v, hv, hve⟩ := ht.2.2
    obtain ⟨hut, hst⟩ := hu t ht.1 ht.2.1 ⟨v, hK hv, hve⟩
    have : u t = v := arc_injOn harc hut (hK hv) (hst.trans hve.symm)
    exact ⟨this ▸ hv, hst⟩
  have hC : ∀ t, t ∈ lifetime f M x → 0 < t → s (u t) = flow f M t x → u t ∈ Icc m m' →
      t ∈ Cr f M s m m' x := fun t h1 h2 h3 h4 => ⟨h1, h2, ⟨u t, h4, h3⟩⟩
  have hn : c - a ≤ (⌈(c - a) / δ⌉₊ : ℝ) * δ := by
    have := Nat.le_ceil ((c - a) / δ)
    rwa [div_le_iff₀ hδ] at this
  exact all_tri hM hf harc hK hδ hU hv _ a (hC a ha.1 ha.2.1 hsa hma) b
    (hC b hb.1 hb.2.1 hsb hmb) c (hC c hc.1 hc.2.1 hsc hmc) hab hbc hn

end PBF


/-! Tools for Lemma 7.15: restricting transversal arcs, concatenating arcs, arcs along a
half-orbit closed up by its limit point, convergence to a unique limit point, the order of the
intersections of an orbit with a transversal arc through a point of its `ω₊`-limit set, and short
flow tubes avoiding a closed set. -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

section concat

variable {E : Type*} [TopologicalSpace E]

/-- Concatenation of two paths parametrized by `[0, 1]`. -/
noncomputable def cc (g h : ℝ → E) (θ : ℝ) : E := if θ ≤ 1 / 2 then g (2 * θ) else h (2 * θ - 1)

lemma cc_props {g h : ℝ → E} (hg : ContinuousOn g (Icc 0 1)) (hh : ContinuousOn h (Icc 0 1))
    (hgi : InjOn g (Icc 0 1)) (hhi : InjOn h (Icc 0 1)) (hj : g 1 = h 0)
    (hd : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, g a = h b → a = 1) :
    ContinuousOn (cc g h) (Icc 0 1) ∧ InjOn (cc g h) (Icc 0 1) ∧ cc g h 0 = g 0 ∧
      cc g h 1 = h 1 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (∃ a ∈ Icc (0 : ℝ) 1, cc g h θ = g a) ∨
        (∃ b ∈ Icc (0 : ℝ) 1, cc g h θ = h b)) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∃ θ ∈ Icc (0 : ℝ) 1, cc g h θ = g a) ∧
      (∀ b ∈ Icc (0 : ℝ) 1, ∃ θ ∈ Icc (0 : ℝ) 1, cc g h θ = h b) := by
  have hlo : ∀ θ, θ ≤ 1 / 2 → cc g h θ = g (2 * θ) := fun θ hθ => if_pos hθ
  have hhi' : ∀ θ, 1 / 2 ≤ θ → cc g h θ = h (2 * θ - 1) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ with h1 | h1
    · rw [← h1, hlo _ le_rfl]; norm_num; exact hj
    · exact if_neg (not_le.mpr h1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hs : Icc (0 : ℝ) 1 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 1 := by
      rw [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
    rw [hs]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · refine ContinuousOn.congr (f := fun θ => g (2 * θ)) ?_ (fun θ hθ => hlo θ hθ.2)
      exact hg.comp (by fun_prop : Continuous fun θ : ℝ => 2 * θ).continuousOn
        (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    · refine ContinuousOn.congr (f := fun θ => h (2 * θ - 1)) ?_ (fun θ hθ => hhi' θ hθ.1)
      exact hh.comp (by fun_prop : Continuous fun θ : ℝ => 2 * θ - 1).continuousOn
        (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  · have key : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ θ' ∈ Icc (0 : ℝ) 1, θ ≤ 1 / 2 → 1 / 2 < θ' →
        cc g h θ ≠ cc g h θ' := by
      intro θ hθ θ' hθ' h1 h2 heq
      rw [hlo θ h1, hhi' θ' h2.le] at heq
      have hθI : 2 * θ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hθ.1], by linarith⟩
      have hθ'I : 2 * θ' - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hθ'.2]⟩
      have ha := hd _ hθI _ hθ'I heq
      rw [ha, hj] at heq
      have := hhi ⟨le_rfl, zero_le_one⟩ hθ'I heq
      linarith
    intro θ hθ θ' hθ' heq
    by_cases h1 : θ ≤ 1 / 2 <;> by_cases h2 : θ' ≤ 1 / 2
    · rw [hlo θ h1, hlo θ' h2] at heq
      have := hgi ⟨by linarith [hθ.1], by linarith⟩ ⟨by linarith [hθ'.1], by linarith⟩ heq
      linarith
    · exact absurd heq (key θ hθ θ' hθ' h1 (not_le.mp h2))
    · exact absurd heq.symm (key θ' hθ' θ hθ h2 (not_le.mp h1))
    · push Not at h1 h2
      rw [hhi' θ h1.le, hhi' θ' h2.le] at heq
      have := hhi ⟨by linarith, by linarith [hθ.2]⟩ ⟨by linarith, by linarith [hθ'.2]⟩ heq
      linarith
  · rw [hlo 0 (by norm_num), mul_zero]
  · rw [hhi' 1 (by norm_num)]; norm_num
  · intro θ hθ
    by_cases h1 : θ ≤ 1 / 2
    · exact Or.inl ⟨2 * θ, ⟨by linarith [hθ.1], by linarith⟩, hlo θ h1⟩
    · push Not at h1
      exact Or.inr ⟨2 * θ - 1, ⟨by linarith, by linarith [hθ.2]⟩, hhi' θ h1.le⟩
  · intro a ha
    refine ⟨a / 2, ⟨by linarith [ha.1], by linarith [ha.2]⟩, ?_⟩
    rw [hlo _ (by linarith [ha.2])]; congr 1; ring
  · intro b hb
    refine ⟨(b + 1) / 2, ⟨by linarith [hb.1], by linarith [hb.2]⟩, ?_⟩
    rw [hhi' _ (by linarith [hb.1])]; congr 1; ring

lemma rev_props {g : ℝ → E} (hg : ContinuousOn g (Icc 0 1)) (hgi : InjOn g (Icc 0 1)) :
    ContinuousOn (fun θ => g (1 - θ)) (Icc 0 1) ∧ InjOn (fun θ => g (1 - θ)) (Icc 0 1) := by
  have hmap : MapsTo (fun θ : ℝ => 1 - θ) (Icc 0 1) (Icc 0 1) := fun θ hθ =>
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  refine ⟨hg.comp (by fun_prop : Continuous fun θ : ℝ => 1 - θ).continuousOn hmap, ?_⟩
  intro θ hθ θ' hθ' heq
  have := hgi (hmap hθ) (hmap hθ') heq
  linarith

end concat

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

/-- Restricting a transversal arc to a smaller open interval. -/
lemma arc_restrict {J J' : Set ℝ} {s : ℝ → Fin 2 → ℝ} (harc : IsTransversalArc f M J s)
    (hJ' : IsOpen J') (hc : J'.OrdConnected) (hne : J'.Nonempty) (hsub : J' ⊆ J) :
    IsTransversalArc f M J' s := by
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := harc
  refine ⟨hJ', hc, hne, h4.mono hsub, ?_, fun t ht => h6 t (hsub ht),
    fun t ht => h7 t (hsub ht)⟩
  have hi : Topology.IsEmbedding (fun t : J' => (⟨t.1, hsub t.2⟩ : J)) := by
    rw [← Topology.IsEmbedding.subtypeVal.of_comp_iff]
    exact Topology.IsEmbedding.subtypeVal
  exact h5.comp hi

/-- A transversal arc through a regular point `y` inside a given ball around `y`. -/
lemma exists_small_arc (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {y : Fin 2 → ℝ} (hy : y ∈ M)
    (hfy : f y ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (J : Set ℝ) (s : ℝ → Fin 2 → ℝ) (c : ℝ), IsTransversalArc f M J s ∧ c ∈ J ∧ s c = y ∧
      ∀ w ∈ J, s w ∈ ball y ρ := by
  obtain ⟨J, s, harc, c, hc, hsc⟩ := exists_arc hM hf hy hfy
  have hsc' : ContinuousAt s c := harc.2.2.2.1.continuousOn.continuousAt (harc.1.mem_nhds hc)
  have hb : ball y ρ ∈ 𝓝 (s c) := by rw [hsc]; exact isOpen_ball.mem_nhds (mem_ball_self hρ)
  have hev : ∀ᶠ w in 𝓝 c, w ∈ J ∧ s w ∈ ball y ρ :=
    (harc.1.eventually_mem hc).and (hsc'.eventually hb)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hsub : Ioo (c - ε) (c + ε) ⊆ J := fun w hw => (hball (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hw.1, hw.2])).1
  refine ⟨Ioo (c - ε) (c + ε), s, c, arc_restrict harc isOpen_Ioo ordConnected_Ioo
    ⟨c, by constructor <;> linarith⟩ hsub, ⟨by linarith, by linarith⟩, hsc, fun w hw => ?_⟩
  exact (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hw.1, hw.2])).2

/-- A forward orbit in a compact set with a single `ω₊`-limit point converges to it. -/
lemma tendsto_of_omega_eq (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {y p : Fin 2 → ℝ}
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKM : K ⊆ M) (hlife : Ici 0 ⊆ lifetime f M y)
    (horb : ∀ t, 0 ≤ t → flow f M t y ∈ K) (hω : omegaLimitSet f M true y = {p}) :
    Tendsto (fun t => flow f M t y) atTop (𝓝 p) := by
  refine hK.tendsto_nhds_of_unique_mapClusterPt (Filter.eventually_atTop.mpr ⟨0, horb⟩) ?_
  intro q hq hcl
  have : q ∈ omegaLimitSet f M true y := by
    rw [omega_true_iff]
    refine ⟨hKM hq, fun ε hε T => ?_⟩
    have h1 := (mapClusterPt_iff_frequently.mp hcl) (ball q ε) (isOpen_ball.mem_nhds
      (mem_ball_self hε))
    obtain ⟨t, ht, htb⟩ := frequently_atTop.mp h1 (max T 0)
    exact ⟨t, le_of_max_le_left ht, hlife (le_of_max_le_right ht), htb⟩
  rw [hω] at this
  exact this

/-- Points with nonempty `ω₊`- and `ω₋`-limit sets are complete. -/
lemma lifetime_univ (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {y a b : Fin 2 → ℝ}
    (ha : a ∈ omegaLimitSet f M true y) (hb : b ∈ omegaLimitSet f M false y) :
    lifetime f M y = univ := by
  have h1 := omega_true_complete ha
  rw [omega_false_eq hM hf] at hb
  have h2 := omega_true_complete hb
  refine eq_univ_of_forall fun t => ?_
  rcases le_total 0 t with ht | ht
  · exact h1 ht
  · have := h2 (show 0 ≤ -t by linarith)
    rw [mem_lifetime_neg, neg_neg] at this
    exact this

/-- The `ω₋` version of `tendsto_of_omega_eq`. -/
lemma tendsto_of_omega_false_eq (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {y p : Fin 2 → ℝ}
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKM : K ⊆ M) (hlife : lifetime f M y = univ)
    (horb : ∀ t, flow f M t y ∈ K) (hω : omegaLimitSet f M false y = {p}) :
    Tendsto (fun t => flow f M t y) atBot (𝓝 p) := by
  rw [omega_false_eq hM hf] at hω
  have hlife' : Ici 0 ⊆ lifetime (fun z => -f z) M y := fun t _ => by
    rw [mem_lifetime_neg, hlife]; trivial
  have h := tendsto_of_omega_eq hM hf.neg hK hKM hlife'
    (fun t _ => by rw [flow_neg hM hf (by rw [hlife]; trivial)]; exact horb _) hω
  have h' : Tendsto (fun t => flow (fun z => -f z) M (-t) y) atBot (𝓝 p) :=
    h.comp tendsto_neg_atBot_atTop
  refine h'.congr (fun t => ?_)
  rw [flow_neg hM hf (by rw [hlife]; trivial), neg_neg]

/-- The arc `[0, 1] → ℝ²` running along the forward orbit of `y` and ending at its limit `p`. -/
noncomputable def hArc (f : (Fin 2 → ℝ) → Fin 2 → ℝ) (M : Set (Fin 2 → ℝ)) (y p : Fin 2 → ℝ)
    (θ : ℝ) : Fin 2 → ℝ :=
  if θ < 1 then flow f M (θ / (1 - θ)) y else p

lemma hArc_props (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {y p : Fin 2 → ℝ}
    (hlife : Ici 0 ⊆ lifetime f M y) (hnp : ¬ IsPeriodicPoint f M y) (hfp : f p = 0)
    (hlim : Tendsto (fun t => flow f M t y) atTop (𝓝 p)) :
    ContinuousOn (hArc f M y p) (Icc 0 1) ∧ InjOn (hArc f M y p) (Icc 0 1) ∧
      hArc f M y p 0 = y ∧ hArc f M y p 1 = p ∧
      ∀ θ ∈ Icc (0 : ℝ) 1, hArc f M y p θ = p ∨ ∃ t, 0 ≤ t ∧ flow f M t y = hArc f M y p θ := by
  replace hlife : ∀ {t : ℝ}, 0 ≤ t → t ∈ lifetime f M y := fun ht => hlife (mem_Ici.mpr ht)
  have h0L : (0 : ℝ) ∈ lifetime f M y := hlife (le_refl 0)
  have hlt : ∀ θ, θ < 1 → hArc f M y p θ = flow f M (θ / (1 - θ)) y := fun θ hθ => if_pos hθ
  have hnn : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → 0 ≤ θ / (1 - θ) := fun θ h1 h2 =>
    div_nonneg h1 (by linarith)
  have hnotp : ∀ t, 0 ≤ t → flow f M t y ≠ p := by
    intro t ht he
    apply hnp
    have hfy : f y = 0 := fixed_of_flow_fixed hM hf (hlife ht) (by rw [he]; exact hfp)
    exact ⟨1, one_pos, hlife zero_le_one, flow_of_fixed hM hf (mem_of_mem_lifetime h0L) hfy 1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · have hc : ContinuousAt (fun θ => flow f M (θ / (1 - θ)) y) θ := by
        have hL := hlife (hnn θ hθ.1 h1)
        exact ContinuousAt.comp (g := fun t => flow f M t y) (f := fun θ : ℝ => θ / (1 - θ))
          ((flow_sol hM hf y) _ hL).2.continuousAt
          (continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by linarith))
      have hev : hArc f M y p =ᶠ[𝓝 θ] fun θ => flow f M (θ / (1 - θ)) y :=
        Filter.eventually_of_mem (Iio_mem_nhds h1) (fun θ' hθ' => hlt θ' hθ')
      exact (hc.congr hev.symm).continuousWithinAt
    · subst h1
      have hlim' : Tendsto (fun θ : ℝ => θ / (1 - θ)) (𝓝[<] 1) atTop := by
        have h1 : Tendsto (fun θ : ℝ => 1 - θ) (𝓝[<] 1) (𝓝[>] 0) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · have : Tendsto (fun θ : ℝ => 1 - θ) (𝓝 1) (𝓝 (1 - 1)) :=
              (continuous_const.sub continuous_id).tendsto 1
            rw [sub_self] at this
            exact this.mono_left nhdsWithin_le_nhds
          · exact eventually_nhdsWithin_of_forall (fun θ hθ => by
              show 0 < 1 - θ; linarith [mem_Iio.mp hθ])
        have h2 : Tendsto (fun θ : ℝ => θ) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
          continuous_id.continuousAt
        exact h2.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp h1) |>.congr
          (fun θ => by simp [div_eq_mul_inv])
      have hcw : ContinuousWithinAt (hArc f M y p) (Iio 1) 1 := by
        show Tendsto _ _ _
        have hv : hArc f M y p 1 = p := if_neg (lt_irrefl 1)
        rw [hv]
        refine (hlim.comp hlim').congr' ?_
        exact eventually_nhdsWithin_of_forall (fun θ hθ => (hlt θ hθ).symm)
      exact (continuousWithinAt_Iio_iff_Iic.mp hcw).mono (fun θ hθ => hθ.2)
  · have key : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ θ' ∈ Icc (0 : ℝ) 1, θ < θ' →
        hArc f M y p θ ≠ hArc f M y p θ' := by
      intro θ hθ θ' hθ' h heq
      have hθ1 : θ < 1 := lt_of_lt_of_le h hθ'.2
      rw [hlt θ hθ1] at heq
      rcases lt_or_eq_of_le hθ'.2 with h1 | h1
      · rw [hlt θ' h1] at heq
        have hmono : θ / (1 - θ) < θ' / (1 - θ') := by
          rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
        exact hnp (periodic_of_eq hM hf (hlife (hnn θ hθ.1 hθ1)) (hlife (hnn θ' hθ'.1 h1))
          hmono heq)
      · subst h1
        rw [show hArc f M y p 1 = p from if_neg (lt_irrefl 1)] at heq
        exact hnotp _ (hnn θ hθ.1 hθ1) heq
    intro θ hθ θ' hθ' heq
    rcases lt_trichotomy θ θ' with h | h | h
    · exact absurd heq (key θ hθ θ' hθ' h)
    · exact h
    · exact absurd heq.symm (key θ' hθ' θ hθ h)
  · rw [hlt 0 one_pos, zero_div]; exact flow_zero hM hf h0L
  · exact if_neg (lt_irrefl 1)
  · intro θ hθ
    rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · exact Or.inr ⟨_, hnn θ hθ.1 h1, (hlt θ h1).symm⟩
    · left; subst h1; exact if_neg (lt_irrefl 1)

section order

variable {x : Fin 2 → ℝ} {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} {c : ℝ}

/-- `(t, w)` is an intersection of the forward orbit of `x` with the arc at time `t`, parameter
`w`. -/
def IsCr (f : (Fin 2 → ℝ) → Fin 2 → ℝ) (M : Set (Fin 2 → ℝ)) (J : Set ℝ)
    (s : ℝ → Fin 2 → ℝ) (x : Fin 2 → ℝ) (t w : ℝ) : Prop :=
  t ∈ lifetime f M x ∧ 0 < t ∧ w ∈ J ∧ s w = flow f M t x

lemma order_of_mono (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (harc : IsTransversalArc f M J s)
    (hc : c ∈ J) (hy : s c ∈ omegaLimitSet f M true x) (hxnp : ¬ IsPeriodicPoint f M x)
    (hxΩ : ∀ t ∈ lifetime f M x, flow f M t x ≠ s c) (u : ℝ → ℝ)
    (hu : ∀ t, t ∈ lifetime f M x → 0 < t → flow f M t x ∈ s '' J →
      u t ∈ J ∧ s (u t) = flow f M t x)
    (hmono : MonotoneOn u {t | t ∈ lifetime f M x ∧ 0 < t ∧ flow f M t x ∈ s '' J}) :
    ∀ t w t' w', IsCr f M J s x t w → IsCr f M J s x t' w' → t < t' → w < w' ∧ w' < c := by
  have hinj := arc_injOn harc
  have hpar : ∀ t w, IsCr f M J s x t w → u t = w := fun t w h =>
    hinj (hu t h.1 h.2.1 ⟨w, h.2.2.1, h.2.2.2⟩).1 h.2.2.1
      ((hu t h.1 h.2.1 ⟨w, h.2.2.1, h.2.2.2⟩).2.trans h.2.2.2.symm)
  have hS : ∀ t w, IsCr f M J s x t w →
      t ∈ {t | t ∈ lifetime f M x ∧ 0 < t ∧ flow f M t x ∈ s '' J} :=
    fun t w h => ⟨h.1, h.2.1, ⟨w, h.2.2.1, h.2.2.2⟩⟩
  -- every intersection lies below `c`
  have hbelow : ∀ t w, IsCr f M J s x t w → w < c := by
    intro t w h
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with heq | hlt
    · exact hxΩ t h.1 (by rw [← h.2.2.2, heq])
    obtain ⟨ε1, hε1, hinv⟩ := arc_inv_cont harc hc (ε := w - c) (by linarith)
    obtain ⟨t', ht'T, ht'L, ⟨w', hw'J, hw'e⟩, hd⟩ := omega_cross hM hf harc hc hy hε1 (t + 1)
    have hcr' : IsCr f M J s x t' w' := ⟨ht'L, by linarith [h.2.1], hw'J, hw'e⟩
    have hmo := hmono (hS t w h) (hS t' w' hcr') (by linarith)
    rw [hpar t w h, hpar t' w' hcr'] at hmo
    have := hinv w' hw'J (by rw [hw'e]; exact hd)
    rw [abs_lt] at this
    linarith [this.2]
  intro t w t' w' h h' htt'
  refine ⟨?_, hbelow t' w' h'⟩
  have hmo := hmono (hS t w h) (hS t' w' h') htt'.le
  rw [hpar t w h, hpar t' w' h'] at hmo
  rcases eq_or_lt_of_le hmo with heq | hlt
  · exfalso
    apply hxnp
    exact periodic_of_eq hM hf h.1 h'.1 htt' (by rw [← h.2.2.2, ← h'.2.2.2, heq])
  · exact hlt

/-- A transversal arc through a point of `ω₊(x)`, oriented so that the intersections of the
forward orbit of `x` move up towards that point. -/
lemma arc_order (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (harc : IsTransversalArc f M J s)
    (hc : c ∈ J) (hy : s c ∈ omegaLimitSet f M true x) (hxnp : ¬ IsPeriodicPoint f M x)
    (hxΩ : ∀ t ∈ lifetime f M x, flow f M t x ≠ s c) :
    ∃ (J' : Set ℝ) (s' : ℝ → Fin 2 → ℝ) (c' : ℝ), IsTransversalArc f M J' s' ∧ c' ∈ J' ∧
      s' c' = s c ∧ (∀ w ∈ J', ∃ v ∈ J, s' w = s v) ∧
      ∀ t w t' w', IsCr f M J' s' x t w → IsCr f M J' s' x t' w' → t < t' →
        w < w' ∧ w' < c' := by
  set u : ℝ → ℝ := fun t => invFunOn s J (flow f M t x) with hudef
  have hu : ∀ t, t ∈ lifetime f M x → 0 < t → flow f M t x ∈ s '' J →
      u t ∈ J ∧ s (u t) = flow f M t x := by
    intro t _ _ h
    obtain ⟨v, hv, hve⟩ := h
    exact invFunOn_pos ⟨v, hv, hve⟩
  rcases mono_true hM hf harc u hu with hmono | hanti
  · exact ⟨J, s, c, harc, hc, rfl, fun w hw => ⟨w, hw, rfl⟩,
      order_of_mono hM hf harc hc hy hxnp hxΩ u hu hmono⟩
  · have harc' := arc_rev harc
    have himg : ∀ z, z ∈ (fun v => s (-v)) '' (Neg.neg ⁻¹' J) ↔ z ∈ s '' J := by
      intro z
      constructor
      · rintro ⟨v, hv, rfl⟩; exact ⟨-v, hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩; exact ⟨-v, by simpa using hv, by simp⟩
    have hc' : -c ∈ Neg.neg ⁻¹' J := by simpa using hc
    have hsc' : (fun v => s (-v)) (-c) = s c := by simp
    refine ⟨Neg.neg ⁻¹' J, fun v => s (-v), -c, harc', hc', hsc', fun w hw => ⟨-w, hw, rfl⟩, ?_⟩
    refine order_of_mono hM hf harc' hc' (by simpa using hy) hxnp
      (by simpa using hxΩ) (fun t => -u t) ?_ ?_
    · intro t h1 h2 h3
      obtain ⟨hJ, he⟩ := hu t h1 h2 ((himg _).mp h3)
      exact ⟨by simpa using hJ, by simpa using he⟩
    · intro a ha b hb hab
      have ha' : a ∈ {t | t ∈ lifetime f M x ∧ 0 < t ∧ flow f M t x ∈ s '' J} :=
        ⟨ha.1, ha.2.1, (himg _).mp ha.2.2⟩
      have hb' : b ∈ {t | t ∈ lifetime f M x ∧ 0 < t ∧ flow f M t x ∈ s '' J} :=
        ⟨hb.1, hb.2.1, (himg _).mp hb.2.2⟩
      exact neg_le_neg (hanti ha' hb' hab)

end order

/-- Short flow tubes over a compact arc piece avoid a closed set disjoint from it. -/
lemma tube_avoid (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ} {s : ℝ → Fin 2 → ℝ}
    (harc : IsTransversalArc f M J s) {m m' : ℝ} (hK : Icc m m' ⊆ J) {Z : Set (Fin 2 → ℝ)}
    (hZ : IsClosed Z) (hdisj : ∀ w ∈ Icc m m', s w ∉ Z) :
    ∃ δ > 0, ∀ w ∈ Icc m m', ∀ τ, |τ| ≤ δ → flow f M τ (s w) ∉ Z := by
  have hP : ∀ w0 ∈ Icc m m', ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), w0), flow f M z.1 (s z.2) ∈ Zᶜ := by
    intro w0 hw0
    have hw0J := hK hw0
    have h0L : (0 : ℝ) ∈ lifetime f M (s w0) := zero_mem_lifetime hM hf (arc_mem harc hw0J)
    have hsc : ContinuousAt s w0 :=
      harc.2.2.2.1.continuousOn.continuousAt (harc.1.mem_nhds hw0J)
    have hin : ContinuousAt (fun q : ℝ × ℝ => (q.1, s q.2)) ((0 : ℝ), w0) :=
      continuousAt_fst.prodMk (ContinuousAt.comp (g := s) (f := Prod.snd) hsc continuousAt_snd)
    have hc : ContinuousAt (fun q : ℝ × ℝ => flow f M q.1 (s q.2)) ((0 : ℝ), w0) :=
      ContinuousAt.comp (g := fun p : ℝ × (Fin 2 → ℝ) => flow f M p.1 p.2)
        (f := fun q : ℝ × ℝ => (q.1, s q.2)) (flow_cont hM hf h0L).2 hin
    refine hc.eventually (hZ.isOpen_compl.mem_nhds ?_)
    show flow f M 0 (s w0) ∉ Z
    rw [flow_zero hM hf h0L]; exact hdisj w0 hw0
  obtain ⟨δ0, hδ0, hball⟩ :=
    Metric.eventually_nhds_iff.mp (isCompact_Icc.eventually_forall_of_forall_eventually
      (P := fun τ w => flow f M τ (s w) ∈ Zᶜ) hP)
  refine ⟨δ0 / 2, by positivity, fun w hw τ hτ => hball ?_ w hw⟩
  rw [Real.dist_eq, sub_zero]
  linarith

end PBF


/-! Lemma 7.15, preparations: non-periodic orbits, short flow tubes meeting complete orbits or a
fixed point, short flow tubes meeting a piece of the orbit of `x`, the two sides of a transversal
arc piece on a Jordan curve, and the choice of consecutive intersections with two arcs. -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

lemma np_inj (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {y : Fin 2 → ℝ}
    (hnp : ¬ IsPeriodicPoint f M y) {t t' : ℝ} (ht : t ∈ lifetime f M y)
    (ht' : t' ∈ lifetime f M y) (heq : flow f M t y = flow f M t' y) : t = t' := by
  rcases lt_trichotomy t t' with h | h | h
  · exact absurd (periodic_of_eq hM hf ht ht' h heq) hnp
  · exact h
  · exact absurd (periodic_of_eq hM hf ht' ht h heq.symm) hnp

lemma np_ne_fixed (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {y q : Fin 2 → ℝ}
    (hnp : ¬ IsPeriodicPoint f M y) {t : ℝ} (ht : t ∈ lifetime f M y) (hq : f q = 0) :
    flow f M t y ≠ q := by
  intro h
  apply hnp
  have hyM : y ∈ M := mem_of_mem_lifetime ht
  have hfy : f y = 0 := fixed_of_flow_fixed hM hf ht (by rw [h]; exact hq)
  exact ⟨1, one_pos, mem_lifetime_of_fixed hyM hfy 1, flow_of_fixed hM hf hyM hfy 1⟩

/-- If `Φ(τ, q) = Φ(t, z)` and `z` is complete, then `q = Φ(t - τ, z)`. -/
lemma flow_eq_shift (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {q z : Fin 2 → ℝ} {τ t : ℝ}
    (hτ : τ ∈ lifetime f M q) (hz : lifetime f M z = univ)
    (heq : flow f M τ q = flow f M t z) : q = flow f M (-τ + t) z := by
  have hback := flow_back hM hf hτ
  calc q = flow f M (-τ) (flow f M τ q) := hback.2.symm
    _ = flow f M (-τ) (flow f M t z) := by rw [heq]
    _ = flow f M (-τ + t) z := flow_flow hM hf (by rw [hz]; trivial) (by rw [hz]; trivial)

/-- A short orbit piece from a point `s w` of an arc meeting `Ω` only at `s c = y` meets the
complete orbits of `y`, `y'` (inside `Ω`, distinct, `y` non-periodic) and a fixed point `p ∈ Ω`
only along the orbit of `y`, and then from `w = c`. -/
lemma tube_omega (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {Ω : Set (Fin 2 → ℝ)} {J : Set ℝ}
    {s : ℝ → Fin 2 → ℝ} {c : ℝ} {y y' p : Fin 2 → ℝ}
    (hsc : s c = y) (hS : ∀ w ∈ J, s w ∈ Ω → w = c) (hyΩ : ∀ t, flow f M t y ∈ Ω)
    (hy'Ω : ∀ t, flow f M t y' ∈ Ω) (hpΩ : p ∈ Ω) (hfp : f p = 0)
    (hLy : lifetime f M y = univ) (hLy' : lifetime f M y' = univ)
    (hnp : ¬ IsPeriodicPoint f M y) (hdis : ∀ t t', flow f M t y ≠ flow f M t' y')
    {w τ : ℝ} (hw : w ∈ J) (hτ : τ ∈ lifetime f M (s w)) :
    flow f M τ (s w) ≠ p ∧ (∀ t, flow f M t y' ≠ flow f M τ (s w)) ∧
      (∀ t, flow f M t y = flow f M τ (s w) → w = c ∧ τ = t) := by
  have h0 : (0 : ℝ) ∈ lifetime f M y := by rw [hLy]; trivial
  have hy0 : flow f M 0 y = y := flow_zero hM hf h0
  refine ⟨fun h => ?_, fun t h => ?_, fun t h => ?_⟩
  · have hpM : p ∈ M := by rw [← h]; exact flow_mem hM hf hτ
    have hsw : s w = p := by
      have hback := flow_back hM hf hτ
      calc s w = flow f M (-τ) (flow f M τ (s w)) := hback.2.symm
        _ = flow f M (-τ) p := by rw [h]
        _ = p := flow_of_fixed hM hf hpM hfp _
    have hwc := hS w hw (by rw [hsw]; exact hpΩ)
    rw [hwc, hsc] at hsw
    exact np_ne_fixed hM hf hnp h0 hfp (by rw [hy0]; exact hsw)
  · have hsw := flow_eq_shift hM hf hτ hLy' h.symm
    have hwc := hS w hw (by rw [hsw]; exact hy'Ω _)
    rw [hwc, hsc] at hsw
    exact hdis 0 _ (by rw [hy0]; exact hsw)
  · have hsw := flow_eq_shift hM hf hτ hLy h.symm
    have hwc := hS w hw (by rw [hsw]; exact hyΩ _)
    refine ⟨hwc, ?_⟩
    rw [hwc, hsc] at hsw
    have := np_inj hM hf hnp (t' := -τ + t) h0 (by rw [hLy]; trivial) (by rw [hy0]; exact hsw)
    linarith

/-- A short orbit piece from a point of the arc piece `s([a, c])` meets the orbit piece
`Φ([t₁, t₂], x)` only from `s a`, if `t*` is the only time in `[t₁ - δ, t₂ + δ]` at which the
orbit of `x` meets `s([a, c])`, at `s a`. -/
lemma tube_orbit (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ} {s : ℝ → Fin 2 → ℝ}
    {a c δ t1 t2 tst : ℝ} {x : Fin 2 → ℝ} (harc : IsTransversalArc f M J s) (hK : Icc a c ⊆ J)
    (hac : a ≤ c)
    (honly : ∀ t ∈ lifetime f M x, t1 - δ ≤ t → t ≤ t2 + δ → flow f M t x ∈ s '' Icc a c →
      t = tst) (hst : flow f M tst x = s a)
    {w τ t' : ℝ} (hw : w ∈ Icc a c) (hτL : τ ∈ lifetime f M (s w)) (hτ : |τ| ≤ δ)
    (ht' : t' ∈ Icc t1 t2) (ht'L : t' ∈ lifetime f M x)
    (heq : flow f M τ (s w) = flow f M t' x) : w = a ∧ t' = tst + τ := by
  have hback := flow_back hM hf hτL
  rw [heq] at hback
  have hL : -τ + t' ∈ lifetime f M x := (mem_lifetime_flow hM hf ht'L).mp hback.1
  have hsw : s w = flow f M (-τ + t') x := by
    calc s w = flow f M (-τ) (flow f M t' x) := hback.2.symm
      _ = flow f M (-τ + t') x := flow_flow hM hf ht'L hL
  have hτb := abs_le.mp hτ
  have := honly _ hL (by linarith [ht'.1]) (by linarith [ht'.2]) ⟨w, hw, hsw⟩
  rw [this, hst] at hsw
  exact ⟨arc_injOn harc (hK hw) (hK ⟨le_rfl, hac⟩) hsw, by linarith⟩

/-- On a Jordan curve containing the arc piece `s([a, c])`, the flow tubes leaving and arriving at
the open arc piece lie in different components. -/
theorem frontier_tubes (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {J : Set ℝ}
    {s : ℝ → Fin 2 → ℝ} (harc : IsTransversalArc f M J s) {a c δ : ℝ} (hac : a < c)
    (hK : Icc a c ⊆ J) (hδ : 0 < δ) {Γ D E : Set (Fin 2 → ℝ)} (hDE : Disjoint D E)
    (hun : D ∪ E = Γᶜ) (hcD : Γ ⊆ closure D) (hcE : Γ ⊆ closure E)
    (hKΓ : ∀ v ∈ Icc a c, s v ∈ Γ) {Tp Tm : Set (Fin 2 → ℝ)}
    (hTp : ∀ w ∈ Ioo a c, ∀ τ ∈ Ioo 0 δ, flow f M τ (s w) ∈ Tp)
    (hTm : ∀ w ∈ Ioo a c, ∀ τ ∈ Ioo (-δ) 0, flow f M τ (s w) ∈ Tm)
    (hp : Tp ⊆ D ∨ Tp ⊆ E) (hm : Tm ⊆ D ∨ Tm ⊆ E) :
    (Tp ⊆ D ∧ Tm ⊆ E) ∨ (Tp ⊆ E ∧ Tm ⊆ D) := by
  have hDC : ∀ Z : Set (Fin 2 → ℝ), Γ ⊆ closure Z → (∀ z ∈ Z, z ∉ Γ) →
      (Z ∩ (Tp ∪ Tm)).Nonempty := by
    intro Z hcl hZΓ
    set w := (a + c) / 2 with hwdef
    have hwI : w ∈ Icc a c := ⟨by linarith, by linarith⟩
    have hwJ := hK hwI
    obtain ⟨ε1, hε1, hinv⟩ := arc_inv_cont harc hwJ (ε := (c - a) / 2) (by linarith)
    obtain ⟨r, hr, hcn⟩ := cross_near hM hf harc hwJ (ε := min δ ε1) (lt_min hδ hε1)
    obtain ⟨z, hzZ, hzd⟩ := Metric.mem_closure_iff.mp (hcl (hKΓ w hwI)) r hr
    obtain ⟨τ, hτ, hτL, ⟨w', hw'J, hw'e⟩, hd⟩ := hcn z (by rw [dist_comm]; exact hzd)
    have hw'w : |w' - w| < (c - a) / 2 :=
      hinv w' hw'J (by rw [hw'e]; exact hd.trans_le (min_le_right _ _))
    obtain ⟨hw1, hw2⟩ := abs_lt.mp hw'w
    have hw'I : w' ∈ Ioo a c := ⟨by linarith, by linarith⟩
    have hzback : flow f M (-τ) (s w') = z := by rw [hw'e]; exact (flow_back hM hf hτL).2
    have hτδ := abs_lt.mp (hτ.trans_le (min_le_left _ _))
    rcases lt_trichotomy τ 0 with hneg | h0 | hpos
    · refine ⟨z, hzZ, Or.inl ?_⟩
      rw [← hzback]; exact hTp w' hw'I (-τ) ⟨by linarith, by linarith⟩
    · exfalso
      apply hZΓ z hzZ
      rw [← hzback, h0, neg_zero, flow_zero' hM hf (arc_mem harc hw'J)]
      exact hKΓ w' ⟨hw'I.1.le, hw'I.2.le⟩
    · refine ⟨z, hzZ, Or.inr ?_⟩
      rw [← hzback]; exact hTm w' hw'I (-τ) ⟨by linarith, by linarith⟩
  have hDΓ : ∀ z ∈ D, z ∉ Γ := fun z hz => by
    have : z ∈ D ∪ E := Or.inl hz
    rw [hun] at this; exact this
  have hEΓ : ∀ z ∈ E, z ∉ Γ := fun z hz => by
    have : z ∈ D ∪ E := Or.inr hz
    rw [hun] at this; exact this
  rcases hp with hp | hp <;> rcases hm with hm | hm
  · exfalso
    obtain ⟨z, hzE, hz | hz⟩ := hDC E hcE hEΓ
    · exact disjoint_left.mp hDE (hp hz) hzE
    · exact disjoint_left.mp hDE (hm hz) hzE
  · exact Or.inl ⟨hp, hm⟩
  · exact Or.inr ⟨hp, hm⟩
  · exfalso
    obtain ⟨z, hzD, hz | hz⟩ := hDC D hcD hDΓ
    · exact disjoint_left.mp hDE hzD (hp hz)
    · exact disjoint_left.mp hDE hzD (hm hz)

/-- Consecutive intersections: an intersection with the first arc at `t₁`, followed by one with
the second arc at `t₂`, with no intersection with either arc in between. -/
theorem choose_times (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin 2 → ℝ}
    (hxc : Ici 0 ⊆ lifetime f M x) {J1 J2 : Set ℝ} {s1 s2 : ℝ → Fin 2 → ℝ} {c1 c2 : ℝ}
    (harc1 : IsTransversalArc f M J1 s1) (harc2 : IsTransversalArc f M J2 s2)
    (hc1 : c1 ∈ J1) (hc2 : c2 ∈ J2) (hdisj : ∀ w ∈ J1, ∀ w' ∈ J2, s1 w ≠ s2 w')
    (hord1 : ∀ t w t' w', IsCr f M J1 s1 x t w → IsCr f M J1 s1 x t' w' → t < t' →
      w < w' ∧ w' < c1)
    (hord2 : ∀ t w t' w', IsCr f M J2 s2 x t w → IsCr f M J2 s2 x t' w' → t < t' →
      w < w' ∧ w' < c2)
    (hlate1 : ∀ T, ∃ t w, T ≤ t ∧ IsCr f M J1 s1 x t w)
    (hlate2 : ∀ T, ∃ t w, T ≤ t ∧ IsCr f M J2 s2 x t w) :
    ∃ t1 a1 t2 a2, IsCr f M J1 s1 x t1 a1 ∧ IsCr f M J2 s2 x t2 a2 ∧ t1 < t2 ∧
      (∀ t w, IsCr f M J1 s1 x t w → t1 < t → t2 < t) ∧
      (∀ t w, IsCr f M J2 s2 x t w → t1 ≤ t → t2 ≤ t) := by
  have hxL : ∀ t : ℝ, 0 ≤ t → t ∈ lifetime f M x := fun t ht => hxc (mem_Ici.mpr ht)
  have hcont : ContinuousOn (fun t => flow f M t x) (Ici 0) := fun t ht =>
    ((flow_sol hM hf x) t (hxL t ht)).2.continuousAt.continuousWithinAt
  obtain ⟨p2, b2, -, hp2⟩ := hlate2 0
  obtain ⟨p1, b1, hp1T, hp1⟩ := hlate1 (p2 + 1)
  obtain ⟨p3, b3, hp3T, hp3⟩ := hlate2 (p1 + 1)
  have hb1 : b1 < c1 := by
    obtain ⟨t, w, ht, h⟩ := hlate1 (p1 + 1)
    have := hord1 p1 b1 t w hp1 h (by linarith)
    linarith [this.1, this.2]
  have hb2 : b2 < c2 := by
    obtain ⟨t, w, ht, h⟩ := hlate2 (p2 + 1)
    have := hord2 p2 b2 t w hp2 h (by linarith)
    linarith [this.1, this.2]
  have hK1 : Icc b1 c1 ⊆ J1 := harc1.2.1.out hp1.2.2.1 hc1
  have hK2 : Icc b2 c2 ⊆ J2 := harc2.2.1.out hp2.2.2.1 hc2
  set K1 := s1 '' Icc b1 c1 with hK1def
  set K2 := s2 '' Icc b2 c2 with hK2def
  have hK1c : IsClosed K1 :=
    (isCompact_Icc.image_of_continuousOn (harc1.2.2.2.1.continuousOn.mono hK1)).isClosed
  have hK2c : IsClosed K2 :=
    (isCompact_Icc.image_of_continuousOn (harc2.2.2.2.1.continuousOn.mono hK2)).isClosed
  have hin1 : ∀ t w, IsCr f M J1 s1 x t w → p1 ≤ t → flow f M t x ∈ K1 := by
    intro t w h ht
    rcases eq_or_lt_of_le ht with heq | hlt
    · subst heq; exact ⟨b1, ⟨le_rfl, hb1.le⟩, hp1.2.2.2⟩
    · have := hord1 p1 b1 t w hp1 h hlt
      exact ⟨w, ⟨this.1.le, this.2.le⟩, h.2.2.2⟩
  have hin2 : ∀ t w, IsCr f M J2 s2 x t w → p2 < t → flow f M t x ∈ K2 := by
    intro t w h ht
    have := hord2 p2 b2 t w hp2 h ht
    exact ⟨w, ⟨this.1.le, this.2.le⟩, h.2.2.2⟩
  have hK12 : ∀ t, flow f M t x ∈ K1 → flow f M t x ∈ K2 → False := by
    rintro t ⟨w, hw, hwe⟩ ⟨w', hw', hw'e⟩
    exact hdisj w (hK1 hw) w' (hK2 hw') (hwe.trans hw'e.symm)
  have hp1pos : 0 < p1 := by linarith [hp2.2.1]
  have hp1K : flow f M p1 x ∈ K1 := hin1 p1 b1 hp1 le_rfl
  -- the first time `t₂ ≥ p₁` in `K₂`
  set S2 := Icc p1 p3 ∩ (fun t => flow f M t x) ⁻¹' K2 with hS2
  have hS2c : IsClosed S2 :=
    (hcont.mono (fun t ht => le_trans hp1pos.le ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc hK2c
  have hp3S : p3 ∈ S2 := ⟨⟨by linarith, le_rfl⟩, hin2 p3 b3 hp3 (by linarith)⟩
  have hS2b : BddBelow S2 := ⟨p1, fun t ht => ht.1.1⟩
  have ht2S : sInf S2 ∈ S2 := hS2c.csInf_mem ⟨p3, hp3S⟩ hS2b
  set t2 := sInf S2 with ht2def
  have hp1t2 : p1 < t2 := by
    rcases eq_or_lt_of_le ht2S.1.1 with h | h
    · exfalso
      have h2 := ht2S.2
      rw [← h] at h2
      exact hK12 p1 hp1K h2
    · exact h
  -- the last time `t₁ ≤ t₂` in `K₁`
  set S1 := Icc p1 t2 ∩ (fun t => flow f M t x) ⁻¹' K1 with hS1
  have hS1c : IsClosed S1 :=
    (hcont.mono (fun t ht => le_trans hp1pos.le ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc hK1c
  have hp1S : p1 ∈ S1 := ⟨⟨le_rfl, hp1t2.le⟩, hp1K⟩
  have hS1b : BddAbove S1 := ⟨t2, fun t ht => ht.1.2⟩
  have ht1S : sSup S1 ∈ S1 := hS1c.csSup_mem ⟨p1, hp1S⟩ hS1b
  set t1 := sSup S1 with ht1def
  have ht12 : t1 < t2 := by
    rcases eq_or_lt_of_le ht1S.1.2 with h | h
    · exfalso
      have h1 := ht1S.2
      rw [h] at h1
      exact hK12 t2 h1 ht2S.2
    · exact h
  have ht1pos : 0 < t1 := by linarith [ht1S.1.1]
  obtain ⟨a1, ha1, ha1e⟩ := ht1S.2
  obtain ⟨a2, ha2, ha2e⟩ := ht2S.2
  refine ⟨t1, a1, t2, a2, ⟨hxL t1 ht1pos.le, ht1pos, hK1 ha1, ha1e⟩,
    ⟨hxL t2 (by linarith), by linarith, hK2 ha2, ha2e⟩, ht12, ?_, ?_⟩
  · intro t w h ht
    by_contra hle
    push Not at hle
    have hK : flow f M t x ∈ K1 := hin1 t w h (by linarith [ht1S.1.1])
    have htS : t ∈ S1 := ⟨⟨by linarith [ht1S.1.1], hle⟩, hK⟩
    linarith [le_csSup hS1b htS]
  · intro t w h ht
    by_contra hlt
    push Not at hlt
    have hK : flow f M t x ∈ K2 := hin2 t w h (by linarith [ht1S.1.1])
    have htS : t ∈ S2 := ⟨⟨by linarith [ht1S.1.1], by linarith [ht2S.1.2]⟩, hK⟩
    linarith [csInf_le hS2b htS]

end PBF


/-! Lemma 7.15, the Jordan curve argument. Two distinct orbits `γ(y₁)`, `γ(y₂)` from `x₋` to `x₊`
in `Ω = ω₊(x)`, transversal arcs `Σᵢ` through `yᵢ`, and consecutive intersections `zᵢ = Φ(tᵢ, x)`
of the orbit of `x` with `Σ₁` and then `Σ₂` give the Jordan curve
`y₁ → z₁ → z₂ → y₂ → x₊ → y₁` (along `Σ₁`, `γ(x)`, `Σ₂`, `γ₊(y₂)`, `γ₊(y₁)` backwards).
The backward half-orbits of `y₁`, `y₂` avoid it and tend to `x₋`, so the flow tubes arriving at
`Σ₁` and at `Σ₂` lie in the component of `x₋`; the tube leaving `Σ₂` lies in the other one. After
`t₂` the orbit of `x` starts in the leaving tube of `Σ₂` and must arrive at its next intersection
with `Σ₁ ∪ Σ₂` (inside the arc pieces) through an arriving tube: a contradiction. -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

variable {f : (Fin 2 → ℝ) → Fin 2 → ℝ} {M : Set (Fin 2 → ℝ)}

lemma lerp_mem {a b θ : ℝ} (hab : a ≤ b) (hθ : θ ∈ Icc (0 : ℝ) 1) : a + θ * (b - a) ∈ Icc a b :=
  ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩

lemma lerp_mem' {a b θ : ℝ} (hab : a ≤ b) (hθ : θ ∈ Icc (0 : ℝ) 1) : b + θ * (a - b) ∈ Icc a b :=
  ⟨by nlinarith [hθ.2], by nlinarith [hθ.1]⟩

lemma lerp_inj {a b θ θ' : ℝ} (hab : a ≠ b) (h : a + θ * (b - a) = a + θ' * (b - a)) : θ = θ' := by
  have h' : (θ - θ') * (b - a) = 0 := by linarith
  rcases mul_eq_zero.mp h' with h' | h'
  · linarith
  · exact absurd (by linarith) hab

/-- The arc `y₁ → z₁ → z₂ → y₂` along `Σ₁`, the orbit of `x` and `Σ₂`. -/
theorem arcB (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {x : Fin 2 → ℝ}
    (hxnp : ¬ IsPeriodicPoint f M x) (hxL : ∀ t : ℝ, 0 ≤ t → t ∈ lifetime f M x)
    {J1 J2 : Set ℝ} {s1 s2 : ℝ → Fin 2 → ℝ} {a1 c1 a2 c2 t1 t2 : ℝ}
    (harc1 : IsTransversalArc f M J1 s1) (harc2 : IsTransversalArc f M J2 s2)
    (hK1 : Icc a1 c1 ⊆ J1) (hK2 : Icc a2 c2 ⊆ J2) (hac1 : a1 < c1) (hac2 : a2 < c2)
    (ht1p : 0 < t1) (h12 : t1 < t2)
    (hz1 : flow f M t1 x = s1 a1) (hz2 : flow f M t2 x = s2 a2)
    (hdisj : ∀ w ∈ J1, ∀ w' ∈ J2, s1 w ≠ s2 w')
    (honly1 : ∀ t ∈ Icc t1 t2, flow f M t x ∈ s1 '' Icc a1 c1 → t = t1)
    (honly2 : ∀ t ∈ Icc t1 t2, flow f M t x ∈ s2 '' Icc a2 c2 → t = t2) :
    ∃ B : ℝ → Fin 2 → ℝ, ContinuousOn B (Icc 0 1) ∧ InjOn B (Icc 0 1) ∧ B 0 = s1 c1 ∧
      B 1 = s2 c2 ∧ (∀ θ ∈ Icc (0 : ℝ) 1, (∃ v ∈ Icc a1 c1, s1 v = B θ) ∨
        (∃ t' ∈ Icc t1 t2, flow f M t' x = B θ) ∨ (∃ v ∈ Icc a2 c2, s2 v = B θ)) ∧
      ∀ v ∈ Icc a2 c2, ∃ θ ∈ Icc (0 : ℝ) 1, B θ = s2 v := by
  have hinj1 := arc_injOn harc1
  have hinj2 := arc_injOn harc2
  have hcx : ∀ t, 0 ≤ t → ContinuousAt (fun t => flow f M t x) t := fun t ht =>
    ((flow_sol hM hf x) t (hxL t ht)).2.continuousAt
  set B1 : ℝ → Fin 2 → ℝ := fun θ => s1 (c1 + θ * (a1 - c1)) with hB1
  set B2 : ℝ → Fin 2 → ℝ := fun θ => flow f M (t1 + θ * (t2 - t1)) x with hB2
  set B3 : ℝ → Fin 2 → ℝ := fun θ => s2 (a2 + θ * (c2 - a2)) with hB3
  have hB1I : ∀ θ ∈ Icc (0 : ℝ) 1, c1 + θ * (a1 - c1) ∈ Icc a1 c1 := fun θ hθ =>
    lerp_mem' hac1.le hθ
  have hB2I : ∀ θ ∈ Icc (0 : ℝ) 1, t1 + θ * (t2 - t1) ∈ Icc t1 t2 := fun θ hθ =>
    lerp_mem h12.le hθ
  have hB3I : ∀ θ ∈ Icc (0 : ℝ) 1, a2 + θ * (c2 - a2) ∈ Icc a2 c2 := fun θ hθ =>
    lerp_mem hac2.le hθ
  have hB2L : ∀ θ ∈ Icc (0 : ℝ) 1, t1 + θ * (t2 - t1) ∈ lifetime f M x := fun θ hθ =>
    hxL _ (ht1p.le.trans (hB2I θ hθ).1)
  have hB1c : ContinuousOn B1 (Icc 0 1) :=
    harc1.2.2.2.1.continuousOn.comp
      (by fun_prop : Continuous fun θ : ℝ => c1 + θ * (a1 - c1)).continuousOn
      (fun θ hθ => hK1 (hB1I θ hθ))
  have hB2c : ContinuousOn B2 (Icc 0 1) := by
    intro θ hθ
    exact (ContinuousAt.comp (g := fun t => flow f M t x) (f := fun θ : ℝ => t1 + θ * (t2 - t1))
      (hcx _ (ht1p.le.trans (hB2I θ hθ).1)) (by fun_prop)).continuousWithinAt
  have hB3c : ContinuousOn B3 (Icc 0 1) :=
    harc2.2.2.2.1.continuousOn.comp
      (by fun_prop : Continuous fun θ : ℝ => a2 + θ * (c2 - a2)).continuousOn
      (fun θ hθ => hK2 (hB3I θ hθ))
  have hB1i : InjOn B1 (Icc 0 1) := fun θ hθ θ' hθ' heq =>
    lerp_inj hac1.ne' (hinj1 (hK1 (hB1I θ hθ)) (hK1 (hB1I θ' hθ')) heq)
  have hB2i : InjOn B2 (Icc 0 1) := fun θ hθ θ' hθ' heq =>
    lerp_inj h12.ne (np_inj hM hf hxnp (hB2L θ hθ) (hB2L θ' hθ') heq)
  have hB3i : InjOn B3 (Icc 0 1) := fun θ hθ θ' hθ' heq =>
    lerp_inj hac2.ne (hinj2 (hK2 (hB3I θ hθ)) (hK2 (hB3I θ' hθ')) heq)
  have hB12j : B1 1 = B2 0 := by
    simp only [hB1, hB2, one_mul, zero_mul, add_zero]
    rw [hz1]; congr 1; ring
  have hB12d : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, B1 a = B2 b → a = 1 := by
    intro a ha b hb heq
    have := honly1 _ (hB2I b hb) ⟨_, hB1I a ha, heq⟩
    have hb0 : b = 0 := lerp_inj h12.ne (this.trans (by ring))
    rw [hb0, ← hB12j] at heq
    exact hB1i ha ⟨zero_le_one, le_rfl⟩ heq
  obtain ⟨hB12c, hB12i, hB120, hB121, hB12cl, -, -⟩ :=
    cc_props hB1c hB2c hB1i hB2i hB12j hB12d
  have hBj : cc B1 B2 1 = B3 0 := by
    rw [hB121]
    simp only [hB2, hB3, one_mul, zero_mul, add_zero]
    rw [← hz2]; congr 1; ring
  have hBd : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, cc B1 B2 a = B3 b → a = 1 := by
    intro a ha b hb heq
    rcases hB12cl a ha with ⟨a', ha', he⟩ | ⟨b', hb', he⟩
    · exfalso
      rw [he] at heq
      exact hdisj _ (hK1 (hB1I a' ha')) _ (hK2 (hB3I b hb)) heq
    · rw [he] at heq
      have := honly2 _ (hB2I b' hb') ⟨_, hB3I b hb, heq.symm⟩
      have hb1 : b' = 1 := lerp_inj h12.ne (this.trans (by ring))
      rw [hb1, ← hB121] at he
      exact hB12i ha ⟨zero_le_one, le_rfl⟩ he
  obtain ⟨hBc, hBi, hB0, hB1', hBcl, -, hBK⟩ := cc_props hB12c hB3c hB12i hB3i hBj hBd
  refine ⟨cc (cc B1 B2) B3, hBc, hBi, ?_, ?_, ?_, ?_⟩
  · rw [hB0, hB120]; simp only [hB1, zero_mul, add_zero]
  · rw [hB1']; simp only [hB3, one_mul, add_sub_cancel]
  · intro θ hθ
    rcases hBcl θ hθ with ⟨a, ha, he⟩ | ⟨b, hb, he⟩
    · rcases hB12cl a ha with ⟨a', ha', he'⟩ | ⟨b', hb', he'⟩
      · exact Or.inl ⟨_, hB1I a' ha', (he.trans he').symm⟩
      · exact Or.inr (Or.inl ⟨_, hB2I b' hb', (he.trans he').symm⟩)
    · exact Or.inr (Or.inr ⟨_, hB3I b hb, he.symm⟩)
  · intro v hv
    have hθ : (v - a2) / (c2 - a2) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith [hv.1]) (by linarith),
        (div_le_one (by linarith)).mpr (by linarith [hv.2])⟩
    obtain ⟨θ', hθ', he⟩ := hBK _ hθ
    refine ⟨θ', hθ', he.trans ?_⟩
    simp only [hB3]
    congr 1
    rw [div_mul_cancel₀ _ (by linarith : c2 - a2 ≠ 0)]; ring

/-- The arc `y₁ → x₊ → y₂` along the forward half-orbits. -/
theorem arcA (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {xp y1 y2 : Fin 2 → ℝ}
    (hL1 : lifetime f M y1 = univ) (hL2 : lifetime f M y2 = univ)
    (hnp1 : ¬ IsPeriodicPoint f M y1) (hnp2 : ¬ IsPeriodicPoint f M y2) (hfp : f xp = 0)
    (hdis : ∀ t t', flow f M t y1 ≠ flow f M t' y2)
    (hp1 : Tendsto (fun t => flow f M t y1) atTop (𝓝 xp))
    (hp2 : Tendsto (fun t => flow f M t y2) atTop (𝓝 xp)) :
    ∃ A : ℝ → Fin 2 → ℝ, ContinuousOn A (Icc 0 1) ∧ InjOn A (Icc 0 1) ∧ A 0 = y1 ∧ A 1 = y2 ∧
      ∀ θ ∈ Icc (0 : ℝ) 1, A θ = xp ∨ (∃ t, 0 ≤ t ∧ flow f M t y1 = A θ) ∨
        (∃ t, 0 ≤ t ∧ flow f M t y2 = A θ) := by
  have hy1L : ∀ t, t ∈ lifetime f M y1 := fun t => by rw [hL1]; trivial
  have hy2L : ∀ t, t ∈ lifetime f M y2 := fun t => by rw [hL2]; trivial
  have hlife1 : Ici 0 ⊆ lifetime f M y1 := fun t _ => hy1L t
  have hlife2 : Ici 0 ⊆ lifetime f M y2 := fun t _ => hy2L t
  obtain ⟨hH1c, hH1i, hH10, hH11, hH1cl⟩ := hArc_props hM hf hlife1 hnp1 hfp hp1
  obtain ⟨hH2c, hH2i, hH20, hH21, hH2cl⟩ := hArc_props hM hf hlife2 hnp2 hfp hp2
  obtain ⟨hH2rc, hH2ri⟩ := rev_props hH2c hH2i
  have hAj : hArc f M y1 xp 1 = (fun θ => hArc f M y2 xp (1 - θ)) 0 := by
    show hArc f M y1 xp 1 = hArc f M y2 xp (1 - 0)
    rw [sub_zero, hH11, hH21]
  have hAd : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      hArc f M y1 xp a = (fun θ => hArc f M y2 xp (1 - θ)) b → a = 1 := by
    intro a ha b hb heq
    have heq' : hArc f M y1 xp a = hArc f M y2 xp (1 - b) := heq
    have hb' : 1 - b ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
    rcases hH1cl a ha with h | ⟨t, ht, h⟩
    · exact hH1i ha ⟨zero_le_one, le_rfl⟩ (h.trans hH11.symm)
    · exfalso
      rcases hH2cl (1 - b) hb' with h' | ⟨t', ht', h'⟩
      · exact np_ne_fixed hM hf hnp1 (hy1L t) hfp (h.trans (heq'.trans h'))
      · exact hdis t t' (h.trans (heq'.trans h'.symm))
  obtain ⟨hAc, hAi, hA0, hA1, hAcl, -, -⟩ := cc_props hH1c hH2rc hH1i hH2ri hAj hAd
  refine ⟨_, hAc, hAi, by rw [hA0, hH10], ?_, ?_⟩
  · rw [hA1]; show hArc f M y2 xp (1 - 1) = y2; rw [sub_self, hH20]
  · intro θ hθ
    rcases hAcl θ hθ with ⟨a, ha, he⟩ | ⟨b, hb, he⟩
    · rcases hH1cl a ha with h | ⟨t, ht, h⟩
      · exact Or.inl (he.trans h)
      · exact Or.inr (Or.inl ⟨t, ht, h.trans he.symm⟩)
    · have hb' : 1 - b ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
      have he' : cc (hArc f M y1 xp) (fun θ => hArc f M y2 xp (1 - θ)) θ =
          hArc f M y2 xp (1 - b) := he
      rcases hH2cl (1 - b) hb' with h | ⟨t, ht, h⟩
      · exact Or.inl (he'.trans h)
      · exact Or.inr (Or.inr ⟨t, ht, h.trans he'.symm⟩)

theorem core2 (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) {Ω : Set (Fin 2 → ℝ)}
    {x xp xm y1 y2 : Fin 2 → ℝ}
    (hxc : Ici 0 ⊆ lifetime f M x) (hxnp : ¬ IsPeriodicPoint f M x)
    (hxΩ : ∀ t ∈ lifetime f M x, flow f M t x ∉ Ω)
    (hxp : xp ∈ Ω) (hxm : xm ∈ Ω) (hfp : f xp = 0) (hfm : f xm = 0) (hne : xp ≠ xm)
    (hL1 : lifetime f M y1 = univ) (hL2 : lifetime f M y2 = univ)
    (hΩ1 : ∀ t, flow f M t y1 ∈ Ω) (hΩ2 : ∀ t, flow f M t y2 ∈ Ω)
    (hnp1 : ¬ IsPeriodicPoint f M y1) (hnp2 : ¬ IsPeriodicPoint f M y2)
    (hdis : ∀ t t', flow f M t y1 ≠ flow f M t' y2)
    (hp1 : Tendsto (fun t => flow f M t y1) atTop (𝓝 xp))
    (hp2 : Tendsto (fun t => flow f M t y2) atTop (𝓝 xp))
    (hm1 : Tendsto (fun t => flow f M t y1) atBot (𝓝 xm))
    (hm2 : Tendsto (fun t => flow f M t y2) atBot (𝓝 xm))
    {J1 J2 : Set ℝ} {s1 s2 : ℝ → Fin 2 → ℝ} {c1 c2 : ℝ}
    (harc1 : IsTransversalArc f M J1 s1) (harc2 : IsTransversalArc f M J2 s2)
    (hc1 : c1 ∈ J1) (hc2 : c2 ∈ J2) (hs1 : s1 c1 = y1) (hs2 : s2 c2 = y2)
    (hS1 : ∀ w ∈ J1, s1 w ∈ Ω → w = c1) (hS2 : ∀ w ∈ J2, s2 w ∈ Ω → w = c2)
    (hdisj : ∀ w ∈ J1, ∀ w' ∈ J2, s1 w ≠ s2 w')
    (hord1 : ∀ t w t' w', IsCr f M J1 s1 x t w → IsCr f M J1 s1 x t' w' → t < t' →
      w < w' ∧ w' < c1)
    (hord2 : ∀ t w t' w', IsCr f M J2 s2 x t w → IsCr f M J2 s2 x t' w' → t < t' →
      w < w' ∧ w' < c2)
    (hlate1 : ∀ T, ∃ t w, T ≤ t ∧ IsCr f M J1 s1 x t w)
    (hlate2 : ∀ T, ∃ t w, T ≤ t ∧ IsCr f M J2 s2 x t w)
    {t1 a1 t2 a2 : ℝ} (hcr1 : IsCr f M J1 s1 x t1 a1) (hcr2 : IsCr f M J2 s2 x t2 a2)
    (h12 : t1 < t2) (hno1 : ∀ t w, IsCr f M J1 s1 x t w → t1 < t → t2 < t)
    (hno2 : ∀ t w, IsCr f M J2 s2 x t w → t1 ≤ t → t2 ≤ t) : False := by
  ------------------------------------------------------------------ basic facts
  have hxL : ∀ t : ℝ, 0 ≤ t → t ∈ lifetime f M x := fun t ht => hxc (mem_Ici.mpr ht)
  have hy1L : ∀ t, t ∈ lifetime f M y1 := fun t => by rw [hL1]; trivial
  have hy2L : ∀ t, t ∈ lifetime f M y2 := fun t => by rw [hL2]; trivial
  have hy10 : flow f M 0 y1 = y1 := flow_zero hM hf (hy1L 0)
  have hy20 : flow f M 0 y2 = y2 := flow_zero hM hf (hy2L 0)
  have hdis' : ∀ t t', flow f M t y2 ≠ flow f M t' y1 := fun t t' h => hdis t' t h.symm
  have hinj1 := arc_injOn harc1
  have hinj2 := arc_injOn harc2
  have ht1p := hcr1.2.1
  have ht2p : 0 < t2 := by linarith
  have hac1 : a1 < c1 := by
    obtain ⟨t, w, ht, h⟩ := hlate1 (t1 + 1)
    have := hord1 t1 a1 t w hcr1 h (by linarith)
    linarith [this.1, this.2]
  have hac2 : a2 < c2 := by
    obtain ⟨t, w, ht, h⟩ := hlate2 (t2 + 1)
    have := hord2 t2 a2 t w hcr2 h (by linarith)
    linarith [this.1, this.2]
  have hK1 : Icc a1 c1 ⊆ J1 := harc1.2.1.out hcr1.2.2.1 hc1
  have hK2 : Icc a2 c2 ⊆ J2 := harc2.2.1.out hcr2.2.2.1 hc2
  let K1 := s1 '' Icc a1 c1
  let K2 := s2 '' Icc a2 c2
  have hK1c : IsClosed K1 :=
    (isCompact_Icc.image_of_continuousOn (harc1.2.2.2.1.continuousOn.mono hK1)).isClosed
  have hK2c : IsClosed K2 :=
    (isCompact_Icc.image_of_continuousOn (harc2.2.2.2.1.continuousOn.mono hK2)).isClosed
  have hz1 : flow f M t1 x = s1 a1 := hcr1.2.2.2.symm
  have hz2 : flow f M t2 x = s2 a2 := hcr2.2.2.2.symm
  have hz1K1 : flow f M t1 x ∈ K1 := ⟨a1, ⟨le_rfl, hac1.le⟩, hz1.symm⟩
  have hz2K2 : flow f M t2 x ∈ K2 := ⟨a2, ⟨le_rfl, hac2.le⟩, hz2.symm⟩
  have hz1K2 : flow f M t1 x ∉ K2 := by
    rintro ⟨v, hv, hve⟩
    exact hdisj a1 (hK1 ⟨le_rfl, hac1.le⟩) v (hK2 hv) (hz1.symm.trans hve.symm)
  have hz2K1 : flow f M t2 x ∉ K1 := by
    rintro ⟨v, hv, hve⟩
    exact hdisj v (hK1 hv) a2 (hK2 ⟨le_rfl, hac2.le⟩) (hve.trans hz2)
  have hΩK1 : ∀ v ∈ Icc a1 c1, s1 v ∈ Ω → s1 v = y1 := fun v hv h => by
    rw [hS1 v (hK1 hv) h, hs1]
  have hΩK2 : ∀ v ∈ Icc a2 c2, s2 v ∈ Ω → s2 v = y2 := fun v hv h => by
    rw [hS2 v (hK2 hv) h, hs2]
  ------------------------------------------------------------------ constants
  obtain ⟨δ1, hδ1, hU1⟩ := unr hM hf harc1 hK1
  obtain ⟨δ2, hδ2, hU2⟩ := unr hM hf harc2 hK2
  obtain ⟨δ3, hδ3, hA12⟩ := tube_avoid hM hf harc1 hK1 hK2c (fun w hw ⟨v, hv, hve⟩ =>
    hdisj w (hK1 hw) v (hK2 hv) hve.symm)
  obtain ⟨δ4, hδ4, hA21⟩ := tube_avoid hM hf harc2 hK2 hK1c (fun w hw ⟨v, hv, hve⟩ =>
    hdisj v (hK1 hv) w (hK2 hw) hve)
  have hcx : ∀ t, 0 ≤ t → ContinuousAt (fun t => flow f M t x) t := fun t ht =>
    ((flow_sol hM hf x) t (hxL t ht)).2.continuousAt
  obtain ⟨η1, hη1, hN1⟩ := Metric.eventually_nhds_iff.mp
    ((hcx t1 ht1p.le).eventually (hK2c.isOpen_compl.mem_nhds hz1K2))
  obtain ⟨η2, hη2, hN2⟩ := Metric.eventually_nhds_iff.mp
    ((hcx t2 ht2p.le).eventually (hK1c.isOpen_compl.mem_nhds hz2K1))
  obtain ⟨m, hm0, hmb1, hmb2, hmb3, hmb4, hmb5, hmb6, hmb7⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ δ1 ∧ m ≤ δ2 ∧
      m ≤ δ3 ∧ m ≤ δ4 ∧ m ≤ η1 ∧ m ≤ η2 ∧ m ≤ 1 :=
    ⟨min δ1 (min δ2 (min δ3 (min δ4 (min η1 (min η2 1))))),
      lt_min hδ1 (lt_min hδ2 (lt_min hδ3 (lt_min hδ4 (lt_min hη1 (lt_min hη2 one_pos))))),
      by simp only [le_min_iff, le_refl, true_and, and_true, min_le_iff]; simp⟩
  obtain ⟨δ, hδm⟩ : ∃ δ : ℝ, δ = m / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδm]; positivity
  ------------------------------------------------------------------ intersection times near `[t₁, t₂]`
  have honly1 : ∀ t ∈ lifetime f M x, t1 - δ ≤ t → t ≤ t2 + δ → flow f M t x ∈ K1 → t = t1 := by
    intro t htL ht1' ht2' hK
    rcases lt_trichotomy t t1 with h | h | h
    · have := sep hM hf hK1 hU1 htL (hxL t1 ht1p.le) hK hz1K1 h
      linarith
    · exact h
    · exfalso
      by_cases h2 : t ≤ t2
      · obtain ⟨v, hv, hve⟩ := hK
        have := hno1 t v ⟨htL, by linarith, hK1 hv, hve⟩ h
        linarith
      · push Not at h2
        exact hN2 (show dist t t2 < η2 by rw [Real.dist_eq, abs_lt]; constructor <;> linarith) hK
  have honly2 : ∀ t ∈ lifetime f M x, t1 - δ ≤ t → t ≤ t2 + δ → flow f M t x ∈ K2 → t = t2 := by
    intro t htL ht1' ht2' hK
    rcases lt_trichotomy t t2 with h | h | h
    · exfalso
      by_cases h1 : t ≤ t1
      · exact hN1 (show dist t t1 < η1 by rw [Real.dist_eq, abs_lt]; constructor <;> linarith) hK
      · push Not at h1
        obtain ⟨v, hv, hve⟩ := hK
        have := hno2 t v ⟨htL, by linarith, hK2 hv, hve⟩ h1.le
        linarith
    · exact h
    · have := sep hM hf hK2 hU2 (hxL t2 ht2p.le) htL hz2K2 hK h
      linarith
  ------------------------------------------------------------------ the Jordan curve
  obtain ⟨B, hBc, hBi, hBy1, hBy2, hBcl', hBK⟩ := arcB hM hf hxnp hxL harc1 harc2 hK1 hK2 hac1
    hac2 ht1p h12 hz1 hz2 hdisj
    (fun t ht hK => honly1 t (hxL t (by linarith [ht.1])) (by linarith [ht.1])
      (by linarith [ht.2]) hK)
    (fun t ht hK => honly2 t (hxL t (by linarith [ht.1])) (by linarith [ht.1])
      (by linarith [ht.2]) hK)
  rw [hs1] at hBy1
  rw [hs2] at hBy2
  obtain ⟨A, hAc, hAi, hA0', hA1', hAcl'⟩ := arcA hM hf hL1 hL2 hnp1 hnp2 hfp hdis hp1 hp2
  have hAΩ : ∀ θ ∈ Icc (0 : ℝ) 1, A θ ∈ Ω := by
    intro θ hθ
    rcases hAcl' θ hθ with h | ⟨t, -, h⟩ | ⟨t, -, h⟩
    · rw [h]; exact hxp
    · rw [← h]; exact hΩ1 t
    · rw [← h]; exact hΩ2 t
  have hBΩ : ∀ θ ∈ Icc (0 : ℝ) 1, B θ ∈ Ω → B θ = y1 ∨ B θ = y2 := by
    intro θ hθ hΩ
    rcases hBcl' θ hθ with ⟨v, hv, h⟩ | ⟨t', ht', h⟩ | ⟨v, hv, h⟩
    · rw [← h] at hΩ ⊢; exact Or.inl (hΩK1 v hv hΩ)
    · exact absurd (h ▸ hΩ) (hxΩ t' (hxL t' (by linarith [ht'.1])))
    · rw [← h] at hΩ ⊢; exact Or.inr (hΩK2 v hv hΩ)
  have hAB : ∀ x' ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1, A x' = B y' → x' = 0 ∨ x' = 1 := by
    intro x' hx' y' hy' heq
    rcases hBΩ y' hy' (heq ▸ hAΩ x' hx') with h | h
    · left; exact hAi hx' ⟨le_rfl, zero_le_one⟩ ((heq.trans h).trans hA0'.symm)
    · right; exact hAi hx' ⟨zero_le_one, le_rfl⟩ ((heq.trans h).trans hA1'.symm)
  obtain ⟨D, E, hDo, hEo, hDE, hun, hcD, hcE⟩ :=
    jordan_arcs A B hAc hBc hAi hBi (hA0'.trans hBy1.symm) (hA1'.trans hBy2.symm) hAB
  let Γ := A '' Icc 0 1 ∪ B '' Icc 0 1
  have hΓ : ∀ z ∈ Γ, (z = xp ∨ (∃ t, 0 ≤ t ∧ flow f M t y1 = z) ∨
      (∃ t, 0 ≤ t ∧ flow f M t y2 = z)) ∨ (∃ v ∈ Icc a1 c1, s1 v = z) ∨
      (∃ t' ∈ Icc t1 t2, flow f M t' x = z) ∨ (∃ v ∈ Icc a2 c2, s2 v = z) := by
    rintro z (⟨θ, hθ, rfl⟩ | ⟨θ, hθ, rfl⟩)
    · exact Or.inl (hAcl' θ hθ)
    · exact Or.inr (hBcl' θ hθ)
  have hΓΩ : ∀ z ∈ Γ, z ∈ Ω → z = xp ∨ (∃ t, 0 ≤ t ∧ flow f M t y1 = z) ∨
      (∃ t, 0 ≤ t ∧ flow f M t y2 = z) := by
    intro z hz hzΩ
    rcases hΓ z hz with h | ⟨v, hv, h⟩ | ⟨t', ht', h⟩ | ⟨v, hv, h⟩
    · exact h
    · rw [← h] at hzΩ ⊢
      exact Or.inr (Or.inl ⟨0, le_rfl, by rw [hy10, hΩK1 v hv hzΩ]⟩)
    · exact absurd (h ▸ hzΩ) (hxΩ t' (hxL t' (by linarith [ht'.1])))
    · rw [← h] at hzΩ ⊢
      exact Or.inr (Or.inr ⟨0, le_rfl, by rw [hy20, hΩK2 v hv hzΩ]⟩)
  have hK2Γ : ∀ v ∈ Icc a2 c2, s2 v ∈ Γ := fun v hv => by
    obtain ⟨θ, hθ, he⟩ := hBK v hv
    exact Or.inr ⟨θ, hθ, he⟩
  have hside : ∀ Z : Set (Fin 2 → ℝ), IsPreconnected Z → (∀ z ∈ Z, z ∉ Γ) → Z ⊆ D ∨ Z ⊆ E :=
    fun Z hZ hZΓ => hZ.subset_or_subset hDo hEo hDE (fun z hz => by rw [hun]; exact hZΓ z hz)
  ------------------------------------------------------------------ the flow tubes
  let F1 : ℝ × ℝ → Fin 2 → ℝ := fun q => flow f M q.2 (s1 q.1)
  let F2 : ℝ × ℝ → Fin 2 → ℝ := fun q => flow f M q.2 (s2 q.1)
  have hFc1 : ∀ q : ℝ × ℝ, q.1 ∈ Icc a1 c1 → |q.2| ≤ δ1 → ContinuousAt F1 q := by
    intro q hq1 hq2
    have hqL := (hU1 q.1 hq1 q.2 hq2).1
    have hc := (flow_cont hM hf hqL).2
    have hsc : ContinuousAt s1 q.1 :=
      harc1.2.2.2.1.continuousOn.continuousAt (harc1.1.mem_nhds (hK1 hq1))
    have hin : ContinuousAt (fun q : ℝ × ℝ => (q.2, s1 q.1)) q :=
      continuousAt_snd.prodMk (ContinuousAt.comp (g := s1) (f := Prod.fst) hsc continuousAt_fst)
    exact ContinuousAt.comp (g := fun p : ℝ × (Fin 2 → ℝ) => flow f M p.1 p.2)
      (f := fun q : ℝ × ℝ => (q.2, s1 q.1)) hc hin
  have hFc2 : ∀ q : ℝ × ℝ, q.1 ∈ Icc a2 c2 → |q.2| ≤ δ2 → ContinuousAt F2 q := by
    intro q hq1 hq2
    have hqL := (hU2 q.1 hq1 q.2 hq2).1
    have hc := (flow_cont hM hf hqL).2
    have hsc : ContinuousAt s2 q.1 :=
      harc2.2.2.2.1.continuousOn.continuousAt (harc2.1.mem_nhds (hK2 hq1))
    have hin : ContinuousAt (fun q : ℝ × ℝ => (q.2, s2 q.1)) q :=
      continuousAt_snd.prodMk (ContinuousAt.comp (g := s2) (f := Prod.fst) hsc continuousAt_fst)
    exact ContinuousAt.comp (g := fun p : ℝ × (Fin 2 → ℝ) => flow f M p.1 p.2)
      (f := fun q : ℝ × ℝ => (q.2, s2 q.1)) hc hin
  -- where short orbit pieces from the arc pieces meet the curve
  have hT1 : ∀ w ∈ Icc a1 c1, ∀ τ, τ ≠ 0 → |τ| ≤ δ → flow f M τ (s1 w) ∈ Γ →
      (w = c1 ∧ 0 < τ) ∨ (w = a1 ∧ 0 < τ) := by
    intro w hw τ hτ0 hτ hmem
    have hτL := (hU1 w hw τ (by linarith)).1
    have hO := tube_omega hM hf (Ω := Ω) hs1 hS1 hΩ1 hΩ2 hxp hfp hL1 hL2 hnp1 hdis (hK1 hw)
      hτL
    rcases hΓ _ hmem with (h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩) | ⟨v, hv, h⟩ | ⟨t', ht', h⟩ | ⟨v, hv, h⟩
    · exact absurd h hO.1
    · obtain ⟨hwc, hτt⟩ := hO.2.2 t h
      exact Or.inl ⟨hwc, lt_of_le_of_ne (by linarith) (Ne.symm hτ0)⟩
    · exact absurd h (hO.2.1 t)
    · exact absurd ⟨v, hK1 hv, h⟩ ((hU1 w hw τ (by linarith)).2 hτ0)
    · obtain ⟨hwa, ht'e⟩ := tube_orbit hM hf harc1 hK1 hac1.le honly1 hz1 hw hτL hτ ht'
        (hxL t' (by linarith [ht'.1])) h.symm
      exact Or.inr ⟨hwa, lt_of_le_of_ne (by linarith [ht'.1]) (Ne.symm hτ0)⟩
    · exact absurd ⟨v, hv, h⟩ (hA12 w hw τ (by linarith))
  have hT2 : ∀ w ∈ Icc a2 c2, ∀ τ, τ ≠ 0 → |τ| ≤ δ → flow f M τ (s2 w) ∈ Γ →
      (w = c2 ∧ 0 < τ) ∨ (w = a2 ∧ τ < 0) := by
    intro w hw τ hτ0 hτ hmem
    have hτL := (hU2 w hw τ (by linarith)).1
    have hO := tube_omega hM hf (Ω := Ω) hs2 hS2 hΩ2 hΩ1 hxp hfp hL2 hL1 hnp2 hdis' (hK2 hw)
      hτL
    rcases hΓ _ hmem with (h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩) | ⟨v, hv, h⟩ | ⟨t', ht', h⟩ | ⟨v, hv, h⟩
    · exact absurd h hO.1
    · exact absurd h (hO.2.1 t)
    · obtain ⟨hwc, hτt⟩ := hO.2.2 t h
      exact Or.inl ⟨hwc, lt_of_le_of_ne (by linarith) (Ne.symm hτ0)⟩
    · exact absurd ⟨v, hv, h⟩ (hA21 w hw τ (by linarith))
    · obtain ⟨hwa, ht'e⟩ := tube_orbit hM hf harc2 hK2 hac2.le honly2 hz2 hw hτL hτ ht'
        (hxL t' (by linarith [ht'.1])) h.symm
      exact Or.inr ⟨hwa, lt_of_le_of_ne (by linarith [ht'.2]) hτ0⟩
    · exact absurd ⟨v, hK2 hv, h⟩ ((hU2 w hw τ (by linarith)).2 hτ0)
  let T1m := F1 '' (Ioc a1 c1 ×ˢ Ioo (-δ) 0)
  let T2m := F2 '' (Ioc a2 c2 ×ˢ Ioo (-δ) 0)
  let T2p := F2 '' (Ico a2 c2 ×ˢ Ioo 0 δ)
  have hT1mc : IsPreconnected T1m := by
    refine ((convex_Ioc a1 c1).prod (convex_Ioo (-δ) 0)).isPreconnected.image F1 ?_
    intro q hq
    exact (hFc1 q ⟨hq.1.1.le, hq.1.2⟩
      (abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩)).continuousWithinAt
  have hT2mc : IsPreconnected T2m := by
    refine ((convex_Ioc a2 c2).prod (convex_Ioo (-δ) 0)).isPreconnected.image F2 ?_
    intro q hq
    exact (hFc2 q ⟨hq.1.1.le, hq.1.2⟩
      (abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩)).continuousWithinAt
  have hT2pc : IsPreconnected T2p := by
    refine ((convex_Ico a2 c2).prod (convex_Ioo 0 δ)).isPreconnected.image F2 ?_
    intro q hq
    exact (hFc2 q ⟨hq.1.1, hq.1.2.le⟩
      (abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩)).continuousWithinAt
  have hT1mΓ : ∀ z ∈ T1m, z ∉ Γ := by
    rintro z ⟨q, hq, rfl⟩ hzΓ
    rcases hT1 q.1 ⟨hq.1.1.le, hq.1.2⟩ q.2 (ne_of_lt hq.2.2)
      (abs_le.mpr ⟨hq.2.1.le, by linarith [hq.2.2]⟩) hzΓ with ⟨-, h⟩ | ⟨h, -⟩
    · linarith [hq.2.2]
    · linarith [hq.1.1]
  have hT2mΓ : ∀ z ∈ T2m, z ∉ Γ := by
    rintro z ⟨q, hq, rfl⟩ hzΓ
    rcases hT2 q.1 ⟨hq.1.1.le, hq.1.2⟩ q.2 (ne_of_lt hq.2.2)
      (abs_le.mpr ⟨hq.2.1.le, by linarith [hq.2.2]⟩) hzΓ with ⟨-, h⟩ | ⟨h, -⟩
    · linarith [hq.2.2]
    · linarith [hq.1.1]
  have hT2pΓ : ∀ z ∈ T2p, z ∉ Γ := by
    rintro z ⟨q, hq, rfl⟩ hzΓ
    rcases hT2 q.1 ⟨hq.1.1, hq.1.2.le⟩ q.2 (ne_of_gt hq.2.1)
      (abs_le.mpr ⟨by linarith [hq.2.1], hq.2.2.le⟩) hzΓ with ⟨h, -⟩ | ⟨-, h⟩
    · linarith [hq.1.2]
    · linarith [hq.2.1]
  have hfr := frontier_tubes hM hf harc2 hac2 hK2 hδ hDE hun hcD hcE hK2Γ (Tp := T2p) (Tm := T2m)
    (fun w hw τ hτ => ⟨(w, τ), ⟨⟨hw.1.le, hw.2⟩, hτ⟩, rfl⟩)
    (fun w hw τ hτ => ⟨(w, τ), ⟨⟨hw.1, hw.2.le⟩, hτ⟩, rfl⟩)
    (hside T2p hT2pc hT2pΓ) (hside T2m hT2mc hT2mΓ)
  ------------------------------------------------------------------ the backward half-orbits
  let Bk1 := (fun t => flow f M t y1) '' Iio 0
  let Bk2 := (fun t => flow f M t y2) '' Iio 0
  have hBk1c : IsPreconnected Bk1 := isPreconnected_Iio.image _ (fun t _ =>
    ((flow_sol hM hf y1) t (hy1L t)).2.continuousAt.continuousWithinAt)
  have hBk2c : IsPreconnected Bk2 := isPreconnected_Iio.image _ (fun t _ =>
    ((flow_sol hM hf y2) t (hy2L t)).2.continuousAt.continuousWithinAt)
  have hBk1Γ : ∀ z ∈ Bk1, z ∉ Γ := by
    rintro z ⟨t, ht, rfl⟩ hzΓ
    rcases hΓΩ _ hzΓ (hΩ1 t) with h | ⟨t', ht', h⟩ | ⟨t', ht', h⟩
    · exact np_ne_fixed hM hf hnp1 (hy1L t) hfp h
    · have := np_inj hM hf hnp1 (hy1L t') (hy1L t) h
      linarith [mem_Iio.mp ht]
    · exact hdis' t' t h
  have hBk2Γ : ∀ z ∈ Bk2, z ∉ Γ := by
    rintro z ⟨t, ht, rfl⟩ hzΓ
    rcases hΓΩ _ hzΓ (hΩ2 t) with h | ⟨t', ht', h⟩ | ⟨t', ht', h⟩
    · exact np_ne_fixed hM hf hnp2 (hy2L t) hfp h
    · exact hdis t' t h
    · have := np_inj hM hf hnp2 (hy2L t') (hy2L t) h
      linarith [mem_Iio.mp ht]
  have hxmΓ : xm ∉ Γ := by
    intro hzΓ
    rcases hΓΩ _ hzΓ hxm with h | ⟨t, -, h⟩ | ⟨t, -, h⟩
    · exact hne h.symm
    · exact np_ne_fixed hM hf hnp1 (hy1L t) hfm h
    · exact np_ne_fixed hM hf hnp2 (hy2L t) hfm h
  have hpt1 : flow f M (-(δ / 2)) y1 ∈ T1m ∩ Bk1 :=
    ⟨⟨(c1, -(δ / 2)), ⟨⟨hac1, le_rfl⟩, ⟨by linarith, by linarith⟩⟩,
      by show flow f M (-(δ / 2)) (s1 c1) = _; rw [hs1]⟩,
      ⟨-(δ / 2), by show -(δ / 2) < 0; linarith, rfl⟩⟩
  have hpt2 : flow f M (-(δ / 2)) y2 ∈ T2m ∩ Bk2 :=
    ⟨⟨(c2, -(δ / 2)), ⟨⟨hac2, le_rfl⟩, ⟨by linarith, by linarith⟩⟩,
      by show flow f M (-(δ / 2)) (s2 c2) = _; rw [hs2]⟩,
      ⟨-(δ / 2), by show -(δ / 2) < 0; linarith, rfl⟩⟩
  ------------------------------------------------------------------ the next intersection after `t₂`
  obtain ⟨t4, w4, ht4, hcr4⟩ := hlate2 (t2 + 1)
  have hw4 := hord2 t2 a2 t4 w4 hcr2 hcr4 (by linarith)
  have ht4K : flow f M t4 x ∈ K1 ∪ K2 := Or.inr ⟨w4, ⟨hw4.1.le, hw4.2.le⟩, hcr4.2.2.2⟩
  let S := Icc (t2 + δ) t4 ∩ (fun t => flow f M t x) ⁻¹' (K1 ∪ K2)
  have hSc : IsClosed S :=
    ContinuousOn.preimage_isClosed_of_isClosed
      (fun t ht => (hcx t (by linarith [ht.1])).continuousWithinAt) isClosed_Icc
      (hK1c.union hK2c)
  have ht4S : t4 ∈ S := ⟨⟨by linarith, le_rfl⟩, ht4K⟩
  have hSb : BddBelow S := ⟨t2 + δ, fun t ht => ht.1.1⟩
  have ht3S : sInf S ∈ S := hSc.csInf_mem ⟨t4, ht4S⟩ hSb
  set t3 := sInf S with ht3def
  have ht3a : t2 + δ ≤ t3 := ht3S.1.1
  have ht3pos : 0 < t3 := by linarith
  have hgap : ∀ t, t2 < t → t < t3 → flow f M t x ∉ K1 ∪ K2 := by
    intro t h1 h2 hK
    by_cases h3 : t < t2 + δ
    · rcases hK with hK | hK
      · exact hN2 (show dist t t2 < η2 by rw [Real.dist_eq, abs_lt]; constructor <;> linarith) hK
      · have := sep hM hf hK2 hU2 (hxL t2 ht2p.le) (hxL t (by linarith)) hz2K2 hK h1
        linarith
    · push Not at h3
      have : t ∈ S := ⟨⟨h3, by linarith [ht3S.1.2]⟩, hK⟩
      linarith [csInf_le hSb this]
  let O := (fun t => flow f M t x) '' Ioo t2 t3
  have hOc : IsPreconnected O := isPreconnected_Ioo.image _ (fun t ht =>
    (hcx t (by linarith [ht.1])).continuousWithinAt)
  have hOΓ : ∀ z ∈ O, z ∉ Γ := by
    rintro z ⟨t, ht, rfl⟩ hzΓ
    have htL := hxL t (by linarith [ht.1])
    rcases hΓ _ hzΓ with (h | ⟨t', -, h⟩ | ⟨t', -, h⟩) | ⟨v, hv, h⟩ | ⟨t', ht', h⟩ | ⟨v, hv, h⟩
    · exact hxΩ t htL (by have h' : flow f M t x = xp := h; rw [h']; exact hxp)
    · exact hxΩ t htL (by have h' : flow f M t' y1 = flow f M t x := h; rw [← h']; exact hΩ1 t')
    · exact hxΩ t htL (by have h' : flow f M t' y2 = flow f M t x := h; rw [← h']; exact hΩ2 t')
    · exact hgap t ht.1 ht.2 (Or.inl ⟨v, hv, h⟩)
    · exact hxnp (periodic_of_eq hM hf (hxL t' (by linarith [ht'.1])) htL
        (by linarith [ht'.2, ht.1]) h)
    · exact hgap t ht.1 ht.2 (Or.inr ⟨v, hv, h⟩)
  have hOp : flow f M (t2 + δ / 2) x ∈ O ∩ T2p := by
    refine ⟨⟨t2 + δ / 2, ⟨by linarith, by linarith⟩, rfl⟩,
      ⟨(a2, δ / 2), ⟨⟨le_rfl, hac2⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩⟩
    show flow f M (δ / 2) (s2 a2) = _
    rw [← hz2, flow_flow hM hf (hxL t2 ht2p.le) (hxL _ (by linarith)), add_comm]
  have hshift : ∀ (s : ℝ → Fin 2 → ℝ) (v : ℝ), s v = flow f M t3 x →
      flow f M (-(δ / 2)) (s v) = flow f M (t3 - δ / 2) x := by
    intro s v hv
    rw [hv, flow_flow hM hf (hxL t3 ht3pos.le) (hxL _ (by linarith))]
    congr 1; ring
  have hO3 : flow f M (t3 - δ / 2) x ∈ O := ⟨t3 - δ / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hTm3 : flow f M (t3 - δ / 2) x ∈ T1m ∨ flow f M (t3 - δ / 2) x ∈ T2m := by
    rcases ht3S.2 with ⟨v, hv, hve⟩ | ⟨v, hv, hve⟩
    · have hvo := hord1 t1 a1 t3 v hcr1 ⟨hxL t3 ht3pos.le, ht3pos, hK1 hv, hve⟩ (by linarith)
      exact Or.inl ⟨(v, -(δ / 2)), ⟨⟨hvo.1, hv.2⟩, ⟨by linarith, by linarith⟩⟩,
        hshift s1 v hve⟩
    · have hvo := hord2 t2 a2 t3 v hcr2 ⟨hxL t3 ht3pos.le, ht3pos, hK2 hv, hve⟩ (by linarith)
      exact Or.inr ⟨(v, -(δ / 2)), ⟨⟨hvo.1, hv.2⟩, ⟨by linarith, by linarith⟩⟩,
        hshift s2 v hve⟩
  ------------------------------------------------------------------ conclusion
  have finish : ∀ W W' : Set (Fin 2 → ℝ), IsOpen W → Disjoint W W' →
      (∀ Z : Set (Fin 2 → ℝ), IsPreconnected Z → (∀ z ∈ Z, z ∉ Γ) → Z ⊆ W ∨ Z ⊆ W') →
      xm ∈ W → ((T2p ⊆ W ∧ T2m ⊆ W') ∨ (T2p ⊆ W' ∧ T2m ⊆ W)) → False := by
    intro W W' hWo hWW' hsd hxmW hfr'
    have inW : ∀ Z : Set (Fin 2 → ℝ), IsPreconnected Z → (∀ z ∈ Z, z ∉ Γ) →
        ∀ z ∈ Z, z ∈ W → Z ⊆ W := by
      intro Z hZ hZΓ z hz hzW
      rcases hsd Z hZ hZΓ with h | h
      · exact h
      · exact absurd (h hz) (disjoint_left.mp hWW' hzW)
    have inW' : ∀ Z : Set (Fin 2 → ℝ), IsPreconnected Z → (∀ z ∈ Z, z ∉ Γ) →
        ∀ z ∈ Z, z ∈ W' → Z ⊆ W' := by
      intro Z hZ hZΓ z hz hzW
      rcases hsd Z hZ hZΓ with h | h
      · exact absurd hzW (disjoint_left.mp hWW' (h hz))
      · exact h
    have hBkW : ∀ y : Fin 2 → ℝ, Tendsto (fun t => flow f M t y) atBot (𝓝 xm) →
        IsPreconnected ((fun t => flow f M t y) '' Iio 0) →
        (∀ z ∈ (fun t => flow f M t y) '' Iio 0, z ∉ Γ) →
        (fun t => flow f M t y) '' Iio 0 ⊆ W := by
      intro y hlim hc hΓ'
      obtain ⟨t, ht1, ht2⟩ :=
        ((hlim.eventually (hWo.mem_nhds hxmW)).and (eventually_lt_atBot (0 : ℝ))).exists
      exact inW _ hc hΓ' _ ⟨t, ht2, rfl⟩ ht1
    have hBk1W := hBkW y1 hm1 hBk1c hBk1Γ
    have hBk2W := hBkW y2 hm2 hBk2c hBk2Γ
    have hT1mW : T1m ⊆ W := inW T1m hT1mc hT1mΓ _ hpt1.1 (hBk1W hpt1.2)
    have hT2mW : T2m ⊆ W := inW T2m hT2mc hT2mΓ _ hpt2.1 (hBk2W hpt2.2)
    have hT2pW' : T2p ⊆ W' := by
      rcases hfr' with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd (h hpt2.1) (disjoint_left.mp hWW' (hT2mW hpt2.1))
      · exact h
    have hOW' : O ⊆ W' := inW' O hOc hOΓ _ hOp.1 (hT2pW' hOp.2)
    rcases hTm3 with h | h
    · exact disjoint_left.mp hWW' (hT1mW h) (hOW' hO3)
    · exact disjoint_left.mp hWW' (hT2mW h) (hOW' hO3)
  have hxmDE : xm ∈ D ∪ E := by rw [hun]; exact hxmΓ
  rcases hxmDE with hD | hE
  · exact finish D E hDo hDE hside hD hfr
  · exact finish E D hEo hDE.symm (fun Z hZ hZΓ => (hside Z hZ hZΓ).symm) hE hfr.symm

end PBF


/-! Lemma 7.15 (`unique_connecting_orbit`): `σ = +` via `PBF.core2`; `σ = -` by time reversal. -/

open Set Filter Topology Metric Function

namespace PBF

open TeschlODE.Planar

theorem unique_true {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M)
    {x : Fin 2 → ℝ} (hx : x ∈ M) (hcpt : IsCompact (omegaLimitSet f M true x))
    {xp xm : Fin 2 → ℝ} (hxp : xp ∈ omegaLimitSet f M true x)
    (hxm : xm ∈ omegaLimitSet f M true x)
    (hfxp : f xp = 0) (hfxm : f xm = 0) (hne : xp ≠ xm)
    {y₁ y₂ : Fin 2 → ℝ}
    (h₁ : orbit f M y₁ ⊆ omegaLimitSet f M true x)
    (h₁p : omegaLimitSet f M true y₁ = {xp}) (h₁m : omegaLimitSet f M false y₁ = {xm})
    (h₂ : orbit f M y₂ ⊆ omegaLimitSet f M true x)
    (h₂p : omegaLimitSet f M true y₂ = {xp}) (h₂m : omegaLimitSet f M false y₂ = {xm}) :
    orbit f M y₁ = orbit f M y₂ := by
  by_contra horb
  set Ω := omegaLimitSet f M true x with hΩdef
  have hΩM : Ω ⊆ M := omega_subset_M true x
  have hxc : Ici 0 ⊆ lifetime f M x := omega_true_complete hxp
  -- `x` is not periodic
  have hxnp : ¬ IsPeriodicPoint f M x := by
    intro hper
    have hΩe := omega_true_periodic hM hf hper
    have h1 : xp ∈ orbit f M x := hΩe ▸ hxp
    have h2 : xm ∈ orbit f M x := hΩe ▸ hxm
    obtain ⟨t, htL, hte⟩ := h1
    obtain ⟨t', ht'L, ht'e⟩ := h2
    have hte' : flow f M t x = xp := hte
    have ht'e' : flow f M t' x = xm := ht'e
    have hfx : f x = 0 := fixed_of_flow_fixed hM hf htL (by rw [hte']; exact hfxp)
    apply hne
    rw [← hte', ← ht'e', flow_of_fixed hM hf hx hfx, flow_of_fixed hM hf hx hfx]
  -- the orbit of `x` avoids `Ω`
  have hxΩ : ∀ t ∈ lifetime f M x, flow f M t x ∉ Ω := by
    intro t htL hΩt
    have hs : 0 < |t| + 1 := by positivity
    have hsL : |t| + 1 ∈ lifetime f M x := hxc (mem_Ici.mpr hs.le)
    have hsL' : |t| + 1 - t + t ∈ lifetime f M x := by rw [sub_add_cancel]; exact hsL
    have hτ : |t| + 1 - t ∈ lifetime f M (flow f M t x) := (mem_lifetime_flow hM hf htL).mpr hsL'
    have h1 : flow f M (|t| + 1 - t) (flow f M t x) ∈ Ω := omega_true_invariant hM hf hΩt hτ
    rw [flow_flow hM hf htL hsL', sub_add_cancel] at h1
    exact hxnp (periodic_of_omegaLimitSet_inter_halfOrbit hM hf true hx
      ⟨_, h1, ⟨|t| + 1, ⟨hsL, by simpa using hs⟩, rfl⟩⟩).1
  -- the connecting orbits
  have hy1p : xp ∈ omegaLimitSet f M true y₁ := by rw [h₁p]; rfl
  have hy1m : xm ∈ omegaLimitSet f M false y₁ := by rw [h₁m]; rfl
  have hy2p : xp ∈ omegaLimitSet f M true y₂ := by rw [h₂p]; rfl
  have hy2m : xm ∈ omegaLimitSet f M false y₂ := by rw [h₂m]; rfl
  have hL1 := lifetime_univ hM hf hy1p hy1m
  have hL2 := lifetime_univ hM hf hy2p hy2m
  have hy1L : ∀ t, t ∈ lifetime f M y₁ := fun t => by rw [hL1]; trivial
  have hy2L : ∀ t, t ∈ lifetime f M y₂ := fun t => by rw [hL2]; trivial
  have hy1M : y₁ ∈ M := mem_of_mem_lifetime (hy1L 0)
  have hy2M : y₂ ∈ M := mem_of_mem_lifetime (hy2L 0)
  have hΩ1 : ∀ t, flow f M t y₁ ∈ Ω := fun t => h₁ ⟨t, hy1L t, rfl⟩
  have hΩ2 : ∀ t, flow f M t y₂ ∈ Ω := fun t => h₂ ⟨t, hy2L t, rfl⟩
  have hy10 : flow f M 0 y₁ = y₁ := flow_zero hM hf (hy1L 0)
  have hy20 : flow f M 0 y₂ = y₂ := flow_zero hM hf (hy2L 0)
  have hy1Ω : y₁ ∈ Ω := by rw [← hy10]; exact hΩ1 0
  have hy2Ω : y₂ ∈ Ω := by rw [← hy20]; exact hΩ2 0
  have hnp1 : ¬ IsPeriodicPoint f M y₁ := by
    intro hper
    have e1 := omega_periodic hM hf true hper
    have e2 := omega_periodic hM hf false hper
    rw [h₁p] at e1
    rw [h₁m] at e2
    exact hne (Set.singleton_eq_singleton_iff.mp (e1.trans e2.symm))
  have hnp2 : ¬ IsPeriodicPoint f M y₂ := by
    intro hper
    have e1 := omega_periodic hM hf true hper
    have e2 := omega_periodic hM hf false hper
    rw [h₂p] at e1
    rw [h₂m] at e2
    exact hne (Set.singleton_eq_singleton_iff.mp (e1.trans e2.symm))
  have hdis : ∀ t t', flow f M t y₁ ≠ flow f M t' y₂ := by
    intro t t' h
    apply horb
    have hm1 : flow f M t y₁ ∈ orbit f M y₁ := ⟨t, hy1L t, rfl⟩
    have hm2 : flow f M t y₁ ∈ orbit f M y₂ := ⟨t', hy2L t', h.symm⟩
    rw [← orbit_eq_of_mem hM hf hm1, orbit_eq_of_mem hM hf hm2]
  have hp1 := tendsto_of_omega_eq hM hf hcpt hΩM (fun t _ => hy1L t) (fun t _ => hΩ1 t) h₁p
  have hp2 := tendsto_of_omega_eq hM hf hcpt hΩM (fun t _ => hy2L t) (fun t _ => hΩ2 t) h₂p
  have hm1 := tendsto_of_omega_false_eq hM hf hcpt hΩM hL1 hΩ1 h₁m
  have hm2 := tendsto_of_omega_false_eq hM hf hcpt hΩM hL2 hΩ2 h₂m
  -- transversal arcs through `y₁`, `y₂` in disjoint balls
  have hreg : ∀ y : Fin 2 → ℝ, y ∈ M → ¬ IsPeriodicPoint f M y → f y ≠ 0 := by
    intro y hy hnp hfy
    exact hnp ⟨1, one_pos, mem_lifetime_of_fixed hy hfy 1, flow_of_fixed hM hf hy hfy 1⟩
  have hy12 : y₁ ≠ y₂ := fun h => hdis 0 0 (by rw [hy10, hy20, h])
  set ρ := dist y₁ y₂ / 2 with hρdef
  have hρ : 0 < ρ := by have := dist_pos.mpr hy12; positivity
  obtain ⟨J1, s1, c1, harc1, hc1, hs1, hball1⟩ :=
    exists_small_arc hM hf hy1M (hreg y₁ hy1M hnp1) hρ
  obtain ⟨J2, s2, c2, harc2, hc2, hs2, hball2⟩ :=
    exists_small_arc hM hf hy2M (hreg y₂ hy2M hnp2) hρ
  obtain ⟨J1', s1', c1', harc1', hc1', hs1', himg1, hord1⟩ :=
    arc_order hM hf harc1 hc1 (by rw [hs1]; exact hy1Ω) hxnp
      (fun t ht h => hxΩ t ht (by rw [h, hs1]; exact hy1Ω))
  obtain ⟨J2', s2', c2', harc2', hc2', hs2', himg2, hord2⟩ :=
    arc_order hM hf harc2 hc2 (by rw [hs2]; exact hy2Ω) hxnp
      (fun t ht h => hxΩ t ht (by rw [h, hs2]; exact hy2Ω))
  rw [hs1] at hs1'
  rw [hs2] at hs2'
  have hdisj : ∀ w ∈ J1', ∀ w' ∈ J2', s1' w ≠ s2' w' := by
    intro w hw w' hw' heq
    obtain ⟨v, hv, hve⟩ := himg1 w hw
    obtain ⟨v', hv', hv'e⟩ := himg2 w' hw'
    have d1 := hball1 v hv
    have d2 := hball2 v' hv'
    rw [← hve, heq, hv'e] at d1
    rw [mem_ball] at d1 d2
    have := dist_triangle y₁ (s2 v') y₂
    rw [dist_comm] at d1
    linarith
  have hS : ∀ (J' : Set ℝ) (s' : ℝ → Fin 2 → ℝ) (c' : ℝ), IsTransversalArc f M J' s' →
      c' ∈ J' → s' c' ∈ Ω → ∀ w ∈ J', s' w ∈ Ω → w = c' := by
    intro J' s' c' harc' hc' hc'Ω w hw hwΩ
    have := omegaLimitSet_inter_arc_subsingleton hM hf true hx harc' ⟨hwΩ, w, hw, rfl⟩
      ⟨hc'Ω, c', hc', rfl⟩
    exact arc_injOn harc' hw hc' this
  have hlate : ∀ (J' : Set ℝ) (s' : ℝ → Fin 2 → ℝ) (c' : ℝ), IsTransversalArc f M J' s' →
      c' ∈ J' → s' c' ∈ Ω → ∀ T, ∃ t w, T ≤ t ∧ IsCr f M J' s' x t w := by
    intro J' s' c' harc' hc' hc'Ω T
    obtain ⟨t, hT, htL, ⟨w, hw, hwe⟩, -⟩ := omega_cross hM hf harc' hc' hc'Ω one_pos (max T 1)
    exact ⟨t, w, le_trans (le_max_left _ _) hT, htL,
      by linarith [le_max_right T 1], hw, hwe⟩
  have hc1Ω : s1' c1' ∈ Ω := by rw [hs1']; exact hy1Ω
  have hc2Ω : s2' c2' ∈ Ω := by rw [hs2']; exact hy2Ω
  have hlate1 := hlate J1' s1' c1' harc1' hc1' hc1Ω
  have hlate2 := hlate J2' s2' c2' harc2' hc2' hc2Ω
  obtain ⟨t1, a1, t2, a2, hcr1, hcr2, h12, hno1, hno2⟩ :=
    choose_times hM hf hxc harc1' harc2' hc1' hc2' hdisj hord1 hord2 hlate1 hlate2
  exact core2 hM hf (Ω := Ω) hxc hxnp hxΩ hxp hxm hfxp hfxm hne hL1 hL2 hΩ1 hΩ2 hnp1 hnp2
    hdis hp1 hp2 hm1 hm2 harc1' harc2' hc1' hc2' hs1' hs2'
    (hS J1' s1' c1' harc1' hc1' hc1Ω) (hS J2' s2' c2' harc2' hc2' hc2Ω) hdisj hord1 hord2
    hlate1 hlate2 hcr1 hcr2 h12 hno1 hno2

end PBF

open TeschlODE.Planar PBF in
theorem solution {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {x : Fin 2 → ℝ} (hx : x ∈ M) (hcpt : IsCompact (omegaLimitSet f M σ x))
    {xp xm : Fin 2 → ℝ} (hxp : xp ∈ omegaLimitSet f M σ x) (hxm : xm ∈ omegaLimitSet f M σ x)
    (hfxp : f xp = 0) (hfxm : f xm = 0) (hne : xp ≠ xm)
    {y₁ y₂ : Fin 2 → ℝ}
    (h₁ : orbit f M y₁ ⊆ omegaLimitSet f M σ x)
    (h₁p : omegaLimitSet f M true y₁ = {xp}) (h₁m : omegaLimitSet f M false y₁ = {xm})
    (h₂ : orbit f M y₂ ⊆ omegaLimitSet f M σ x)
    (h₂p : omegaLimitSet f M true y₂ = {xp}) (h₂m : omegaLimitSet f M false y₂ = {xm}) :
    orbit f M y₁ = orbit f M y₂ := by
  cases σ with
  | true => exact unique_true hM hf hx hcpt hxp hxm hfxp hfxm hne h₁ h₁p h₁m h₂ h₂p h₂m
  | false =>
    have eω : ∀ z, omegaLimitSet f M false z = omegaLimitSet (fun y => -f y) M true z :=
      fun z => omega_false_eq hM hf z
    have eω' : ∀ z, omegaLimitSet (fun y => -f y) M false z = omegaLimitSet f M true z :=
      fun z => by rw [omega_neg hM hf]; rfl
    have eo : ∀ z, orbit (fun y => -f y) M z = orbit f M z := fun z => orbit_neg hM hf z
    rw [eω x] at hcpt hxp hxm h₁ h₂
    rw [eω y₁] at h₁m
    rw [eω y₂] at h₂m
    rw [← eω' y₁] at h₁p
    rw [← eω' y₂] at h₂p
    rw [← eo y₁] at h₁ ⊢
    rw [← eo y₂] at h₂ ⊢
    exact unique_true hM hf.neg hx hcpt hxm hxp (by simp [hfxm]) (by simp [hfxp]) (Ne.symm hne)
      h₁ h₁m h₁p h₂ h₂m h₂p



