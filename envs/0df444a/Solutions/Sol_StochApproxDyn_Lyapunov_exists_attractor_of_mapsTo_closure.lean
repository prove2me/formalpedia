-- Prove2me | solution 1 for StochApproxDyn.Lyapunov.exists_attractor_of_mapsTo_closure
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:13:22.233028+00:00
-- url     : https://prove2.me/submissions/9fd090e3-4b94-43e4-8452-f8effd1cfd2c

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal


namespace StochApproxDyn.Lyapunov

theorem flow_cont_at {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (s : ℝ≥0) :
    Continuous (fun x => Φ s x) := Φ.continuous continuous_const continuous_id

/-- step 1: tube lemma -/
theorem att_step1 {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U K : Set M) (hUo : IsOpen U) (hK : IsCompact K)
    (T : ℝ≥0) (hTU : Φ T '' K ⊆ U) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s : ℝ≥0, T ≤ s → s ≤ T + δ → Φ s '' K ⊆ U := by
  have hn : IsOpen {p : ℝ≥0 × M | Φ p.1 p.2 ∈ U} :=
    hUo.preimage (Φ.continuous continuous_fst continuous_snd)
  have hsub : ({T} : Set ℝ≥0) ×ˢ K ⊆ {p : ℝ≥0 × M | Φ p.1 p.2 ∈ U} := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    exact hTU ⟨x, hx, rfl⟩
  obtain ⟨u, v, hu, hv, hTu, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hn hsub
  have hTu' : T ∈ u := hTu rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu T hTu'
  refine ⟨(ε / 2).toNNReal, by simpa using hε, ?_⟩
  · intro s h1 h2
    rintro _ ⟨x, hx, rfl⟩
    have hs : s ∈ u := by
      apply hball
      rw [Metric.mem_ball, NNReal.dist_eq]
      have h1' : (T : ℝ) ≤ s := h1
      have h2' : (s : ℝ) ≤ T + ε / 2 := by
        have := (NNReal.coe_le_coe.mpr h2)
        rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at this; exact this
      rw [abs_lt]; constructor <;> linarith
    exact huv (Set.mk_mem_prod hs (hKv hx))

theorem att_step3 {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U K : Set M) (hUK : U ⊆ K) (T : ℝ≥0) (hT : 0 < T) (δ : ℝ≥0) (hδ : 0 < δ)
    (hG : ∀ s : ℝ≥0, T ≤ s → s ≤ T + δ → Φ s '' K ⊆ U) :
    ∃ t0 : ℝ≥0, ∀ t : ℝ≥0, t0 ≤ t → Φ t '' K ⊆ U := by
  have hadd : ∀ a b : ℝ≥0, Φ a '' K ⊆ U → Φ b '' K ⊆ U → Φ (a + b) '' K ⊆ U := by
    intro a b ha hb
    rintro _ ⟨x, hx, rfl⟩
    rw [Φ.map_add]
    exact ha ⟨_, hUK (hb ⟨x, hx, rfl⟩), rfl⟩
  have hmul : ∀ h : ℝ≥0, Φ h '' K ⊆ U → ∀ n : ℕ, Φ ((n + 1 : ℕ) * h) '' K ⊆ U := by
    intro h hh n
    induction n with
    | zero => simpa using hh
    | succ k ih =>
      have : ((k + 1 + 1 : ℕ) : ℝ≥0) * h = h + ((k + 1 : ℕ) : ℝ≥0) * h := by push_cast; ring
      rw [this]; exact hadd _ _ hh ih
  refine ⟨((⌈(T : ℝ) / δ⌉₊ : ℕ) + 1 : ℝ≥0) * T, ?_⟩
  intro t ht
  set N := ⌈(T : ℝ) / δ⌉₊ with hN
  set n := ⌊(t : ℝ) / T⌋₊ with hn
  have hTr : (0 : ℝ) < T := hT
  have hδr : (0 : ℝ) < δ := hδ
  have ht' : ((N : ℝ) + 1) * T ≤ t := by
    have := NNReal.coe_le_coe.mpr ht; push_cast at this; exact this
  have hNn : N + 1 ≤ n := by
    rw [hn]; apply Nat.le_floor
    rw [le_div_iff₀ hTr]; push_cast; exact ht'
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hfl1 : (n : ℝ) ≤ t / T := Nat.floor_le (by positivity)
  have hfl2 : (t : ℝ) / T < n + 1 := Nat.lt_floor_add_one _
  have hNle : (T : ℝ) / δ ≤ N := Nat.le_ceil _
  set h : ℝ≥0 := t / (n : ℝ≥0) with hh
  have hhc : (h : ℝ) = t / n := by rw [hh, NNReal.coe_div]; rfl
  have hTh : T ≤ h := by
    rw [← NNReal.coe_le_coe, hhc]
    rw [le_div_iff₀ hnpos]; rw [le_div_iff₀ hTr] at hfl1; linarith
  have hhd : h ≤ T + δ := by
    rw [← NNReal.coe_le_coe, hhc, NNReal.coe_add]
    rw [div_le_iff₀ hnpos]
    rw [div_lt_iff₀ hTr] at hfl2
    rw [div_le_iff₀ hδr] at hNle
    have : (T : ℝ) ≤ n * δ := by
      have : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
      nlinarith
    nlinarith
  have := hmul h (hG h hTh hhd) (n - 1)
  have heq : (((n - 1 + 1 : ℕ)) : ℝ≥0) * h = t := by
    rw [Nat.sub_add_cancel hn1]
    rw [← NNReal.coe_inj]; push_cast; rw [hhc]; field_simp
  rwa [heq] at this

theorem exists_attractor_core {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U : Set M) (hUo : IsOpen U) (hUne : U.Nonempty) (hUc : IsCompact (closure U))
    (T : ℝ≥0) (hT : 0 < T) (hTU : Φ T '' closure U ⊆ U) :
    ∃ A : Set M, StochApproxDyn.LimitSet.IsAttractor Φ A ∧ A ⊆ U ∧
      closure U ⊆ StochApproxDyn.LimitSet.basin Φ A := by
  set K := closure U with hKdef
  have hUK : U ⊆ K := subset_closure
  obtain ⟨δ, hδ, hG⟩ := att_step1 Φ U K hUo hUc T hTU
  obtain ⟨t0, ht0⟩ := att_step3 Φ U K hUK T hT δ hδ hG
  set S : ℝ≥0 → Set M := fun s => Φ s '' K with hS
  have hSc : ∀ s, IsCompact (S s) := fun s => hUc.image (flow_cont_at Φ s)
  have hScl : ∀ s, IsClosed (S s) := fun s => (hSc s).isClosed
  have hSne : ∀ s, (S s).Nonempty := fun s => (hUne.mono hUK).image _
  have hmono : ∀ r s : ℝ≥0, r + t0 ≤ s → S s ⊆ S r := by
    intro r s hrs
    rintro _ ⟨x, hx, rfl⟩
    have : s = r + (s - r) := by
      rw [add_tsub_cancel_of_le]; exact le_trans (le_add_of_nonneg_right zero_le') hrs
    refine ⟨Φ (s - r) x, hUK (ht0 (s - r) ?_ ⟨x, hx, rfl⟩), ?_⟩
    · rw [le_tsub_iff_left (le_trans (le_add_of_nonneg_right zero_le') hrs)]; exact hrs
    · show Φ r (Φ (s - r) x) = Φ s x
      rw [← Φ.map_add, ← this]
  have hdir : Directed (· ⊇ ·) S := by
    intro i j
    refine ⟨max i j + t0, hmono i _ ?_, hmono j _ ?_⟩
    · exact add_le_add (le_max_left _ _) le_rfl
    · exact add_le_add (le_max_right _ _) le_rfl
  set A := ⋂ s, S s with hA
  have hAne : A.Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir hSne hSc hScl
  have hAsub : ∀ s, A ⊆ S s := fun s => Set.iInter_subset _ s
  have hAc : IsCompact A := (hSc 0).of_isClosed_subset (isClosed_iInter hScl) (hAsub 0)
  have hAU : A ⊆ U := (hAsub t0).trans (ht0 t0 le_rfl)
  have hinv : StochApproxDyn.LimitSet.IsInvariantSet Φ A := by
    intro t
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      simp only [hA, Set.mem_iInter]
      intro r
      obtain ⟨x, hx, hxz⟩ := hAsub (r + t0) hz
      refine ⟨Φ (t + t0) x, hUK (ht0 _ (le_add_of_nonneg_left zero_le') ⟨x, hx, rfl⟩), ?_⟩
      show Φ r (Φ (t + t0) x) = Φ t z
      rw [← hxz, ← Φ.map_add, ← Φ.map_add]
      congr 1; ring
    · intro y hy
      set C : ℝ≥0 → Set M := fun s => S s ∩ (fun z => Φ t z) ⁻¹' {y} with hC
      have hCcl : ∀ s, IsClosed (C s) := fun s =>
        (hScl s).inter (isClosed_singleton.preimage (flow_cont_at Φ t))
      have hCc : ∀ s, IsCompact (C s) := fun s => (hSc s).of_isClosed_subset (hCcl s)
        Set.inter_subset_left
      have hCne : ∀ s, (C s).Nonempty := by
        intro s
        obtain ⟨x, hx, hxy⟩ := hAsub (t + s) hy
        refine ⟨Φ s x, ⟨x, hx, rfl⟩, ?_⟩
        show Φ t (Φ s x) = y
        rw [← Φ.map_add]; exact hxy
      have hCdir : Directed (· ⊇ ·) C := by
        intro i j
        refine ⟨max i j + t0, ?_, ?_⟩
        · exact Set.inter_subset_inter_left _ (hmono i _ (add_le_add (le_max_left _ _) le_rfl))
        · exact Set.inter_subset_inter_left _ (hmono j _ (add_le_add (le_max_right _ _) le_rfl))
      obtain ⟨z, hz⟩ :=
        IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hCdir hCne hCc hCcl
      simp only [Set.mem_iInter] at hz
      refine ⟨z, ?_, (hz 0).2⟩
      simp only [hA, Set.mem_iInter]
      intro s; exact (hz s).1
  have hunif : ∀ ε : ℝ, 0 < ε → ∃ t₁ : ℝ≥0, ∀ t : ℝ≥0, t₁ ≤ t → ∀ x ∈ K,
      Metric.infDist (Φ t x) A < ε := by
    intro ε hε
    have : ∃ s, S s ⊆ {y | Metric.infDist y A < ε} := by
      by_contra hcon
      push_neg at hcon
      set D : ℝ≥0 → Set M := fun s => S s ∩ {y | ε ≤ Metric.infDist y A} with hD
      have hDcl : ∀ s, IsClosed (D s) := fun s =>
        (hScl s).inter (isClosed_le continuous_const (Metric.continuous_infDist_pt A))
      have hDc : ∀ s, IsCompact (D s) := fun s => (hSc s).of_isClosed_subset (hDcl s)
        Set.inter_subset_left
      have hDne : ∀ s, (D s).Nonempty := by
        intro s
        obtain ⟨y, hy1, hy2⟩ := Set.not_subset.mp (hcon s)
        exact ⟨y, hy1, show ε ≤ Metric.infDist y A from le_of_not_gt hy2⟩
      have hDdir : Directed (· ⊇ ·) D := by
        intro i j
        refine ⟨max i j + t0, ?_, ?_⟩
        · exact Set.inter_subset_inter_left _ (hmono i _ (add_le_add (le_max_left _ _) le_rfl))
        · exact Set.inter_subset_inter_left _ (hmono j _ (add_le_add (le_max_right _ _) le_rfl))
      obtain ⟨z, hz⟩ :=
        IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed D hDdir hDne hDc hDcl
      simp only [Set.mem_iInter] at hz
      have hzA : z ∈ A := by
        simp only [hA, Set.mem_iInter]; intro s; exact (hz s).1
      have h1 := (hz 0).2
      simp only [Set.mem_setOf_eq, Metric.infDist_zero_of_mem hzA] at h1
      linarith
    obtain ⟨s, hs⟩ := this
    refine ⟨s + t0, fun t ht x hx => hs (hmono s t ht ⟨x, hx, rfl⟩)⟩
  refine ⟨A, ⟨hAne, hAc, hinv, U, hUo.mem_nhdsSet.mpr hAU, ?_⟩, hAU, ?_⟩
  · intro ε hε
    obtain ⟨t₁, h⟩ := hunif ε hε
    exact ⟨t₁, fun t ht x hx => h t ht x (hUK hx)⟩
  · intro x hx
    show Filter.Tendsto (fun t : ℝ≥0 => Metric.infDist (Φ t x) A) Filter.atTop (nhds 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨t₁, h⟩ := hunif ε hε
    refine ⟨t₁, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
    exact h t ht x hx

end StochApproxDyn.Lyapunov

open StochApproxDyn.Lyapunov


theorem solution {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U : Set M) (hUo : IsOpen U) (hUne : U.Nonempty) (hUc : IsCompact (closure U))
    (T : ℝ≥0) (hT : 0 < T) (hTU : Φ T '' closure U ⊆ U) :
    ∃ A : Set M, StochApproxDyn.LimitSet.IsAttractor Φ A ∧ A ⊆ U ∧ closure U ⊆ StochApproxDyn.LimitSet.basin Φ A := by
  exact exists_attractor_core Φ U hUo hUne hUc T hT hTU
