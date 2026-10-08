-- Prove2me | solution 1 for TeschlODE.Planar.omegaLimitSet_eq_periodic_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-06T15:55:35.793702+00:00
-- url     : https://prove2.me/submissions/894caf4b-1655-4645-b163-fe77942a376f

import Mathlib
import Definitions.Def_TeschlODE_Planar_flow
import Definitions.Def_TeschlODE_Planar_orbit
import Definitions.Def_TeschlODE_Planar_halfOrbit
import Definitions.Def_TeschlODE_Planar_omegaLimitSet
import Definitions.Def_TeschlODE_Planar_IsPeriodicPoint
import Definitions.Def_TeschlODE_Planar_IsTransversalArc
import Theorems.Thm_TeschlODE_Planar_omegaLimitSet_inter_arc_subsingleton


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


/-! Lemma 7.14 from Corollary 7.10. -/

open TeschlODE.Planar PBF in
theorem solution {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {x : Fin 2 → ℝ} (hx : x ∈ M)
    (hconn : IsPreconnected (omegaLimitSet f M σ x))
    {y : Fin 2 → ℝ} (hy : IsPeriodicPoint f M y) (hyreg : f y ≠ 0)
    (hsub : orbit f M y ⊆ omegaLimitSet f M σ x) :
    omegaLimitSet f M σ x = orbit f M y :=
  eq_periodic_orbit hM hf (omega_subset_M σ x) (fun _ hz => omega_orbit_subset hM hf σ hz)
    (fun _ _ harc => omegaLimitSet_inter_arc_subsingleton hM hf σ hx harc) hconn hy hyreg hsub

