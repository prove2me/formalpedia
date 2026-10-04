-- Prove2me | solution 1 for TeschlODE.HigherDim.trapping_region_attracting
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:01:30.621529+00:00
-- url     : https://prove2.me/submissions/965bf176-dc85-49bc-b57f-b92b1392ca44

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_omegaPlusSet
import Definitions.Def_TeschlODE_HigherDim_stableSet
import Definitions.Def_TeschlODE_HigherDim_IsInvariant
import Definitions.Def_TeschlODE_HigherDim_IsAttracting
import Definitions.Def_TeschlODE_HigherDim_IsTrappingRegion

open Filter Topology Metric Set TeschlODE.HigherDim

lemma flow_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (s : ℝ) (hs : s ∈ I x) (t : ℝ) (ht : t + s ∈ I x) :
    t ∈ I (Φ s x) ∧ Φ t (Φ s x) = Φ (t + s) x := by
  obtain ⟨⟨hJo, hJc, hJM, hJd⟩, -, -, -⟩ := hΦ x hx
  have hyM : Φ s x ∈ M := hJM s hs
  have hcurve : IsIntegralCurve f M {τ | τ + s ∈ I x} (fun τ => Φ (τ + s) x) := by
    refine ⟨hJo.preimage (continuous_id.add continuous_const), ⟨fun a ha b hb τ hτ => ?_⟩,
      fun τ hτ => hJM _ hτ, fun τ hτ => (hJd _ hτ).comp_add_const τ s⟩
    exact hJc.out ha hb ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  obtain ⟨-, -, -, hmax⟩ := hΦ (Φ s x) hyM
  obtain ⟨hsub, heq⟩ := hmax _ _ hcurve (by simpa using hs) (by simp)
  exact ⟨hsub ht, (heq t ht).symm⟩

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsTrappingRegion M I Φ E) :
    omegaPlusSet M I Φ E = (⋂ t : ℝ, ⋂ (_ : 0 ≤ t), Φ t '' E) ∧
      (omegaPlusSet M I Φ E).Nonempty ∧ IsInvariant M I Φ (omegaPlusSet M I Φ E) ∧
      IsCompact (omegaPlusSet M I Φ E) ∧ IsConnected (omegaPlusSet M I Φ E) ∧
      IsAttracting M I Φ (omegaPlusSet M I Φ E) := by
  obtain ⟨hEo, hEconn, hEc, hEM, hEtrap⟩ := hE
  set C := closure E with hC
  have hloc : LocallyLipschitzOn C f := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (hM.mem_nhds (hEM hx))).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hEc
  have hid : ∀ w ∈ C, Φ 0 w = w := fun w hw => (hΦ w (hEM hw)).2.2.1
  have hnn : ∀ w ∈ C, ∀ t : ℝ, 0 ≤ t → t ∈ I w := by
    intro w hw t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]; exact (hΦ w (hEM hw)).2.1
    · exact (hEtrap w hw t h).1
  have hstay : ∀ w ∈ C, ∀ t : ℝ, 0 ≤ t → Φ t w ∈ C := by
    intro w hw t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, hid w hw]; exact hw
    · exact subset_closure (hEtrap w hw t h).2
  have hcomp : ∀ w ∈ C, ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → Φ t (Φ s w) = Φ (t + s) w := fun w hw s t hs ht =>
    (flow_core f M I Φ hΦ w (hEM hw) s (hnn w hw s hs) t (hnn w hw _ (by linarith))).2
  have hlip : ∀ t : ℝ, 0 ≤ t → ∀ a ∈ C, ∀ b ∈ C,
      dist (Φ t a) (Φ t b) ≤ dist a b * Real.exp (K * t) := by
    intro t ht a ha b hb
    have htraj : ∀ z ∈ C, ContinuousOn (fun τ => Φ τ z) (Icc 0 t) ∧
        (∀ τ ∈ Ico (0 : ℝ) t, HasDerivWithinAt (fun τ => Φ τ z) (f (Φ τ z)) (Ici τ) τ) ∧
        (∀ τ ∈ Ico (0 : ℝ) t, Φ τ z ∈ C) := by
      intro z hz
      obtain ⟨⟨-, hJc, -, hJd⟩, h0, -, -⟩ := hΦ z (hEM hz)
      have hIcc : Icc (0 : ℝ) t ⊆ I z := hJc.out h0 (hnn z hz t ht)
      exact ⟨fun τ hτ => (hJd τ (hIcc hτ)).continuousAt.continuousWithinAt,
        fun τ hτ => (hJd τ (hIcc (Ico_subset_Icc_self hτ))).hasDerivWithinAt,
        fun τ hτ => hstay z hz τ hτ.1⟩
    obtain ⟨c1, d1, m1⟩ := htraj a ha
    obtain ⟨c2, d2, m2⟩ := htraj b hb
    have := dist_le_of_trajectories_ODE_of_mem (v := fun _ => f) (s := fun _ => C)
      (fun _ _ => hK) c1 d1 m1 c2 d2 m2
      (le_of_eq (by rw [hid a ha, hid b hb])) t ⟨ht, le_rfl⟩
    simpa using this
  have hcont : ∀ t : ℝ, 0 ≤ t → ContinuousOn (Φ t) C := by
    intro t ht
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    refine ⟨ε / Real.exp (K * t), div_pos hε (Real.exp_pos _), fun a ha hab => ?_⟩
    calc dist (Φ t a) (Φ t b) ≤ dist a b * Real.exp (K * t) := hlip t ht a ha b hb
      _ < ε / Real.exp (K * t) * Real.exp (K * t) :=
          mul_lt_mul_of_pos_right hab (Real.exp_pos _)
      _ = ε := div_mul_cancel₀ ε (Real.exp_pos _).ne'
  -- the set `Λ = ⋂_{t ≥ 0} Φ_t(closure E)`
  set Λ := ⋂ t : ℝ, ⋂ (_ : 0 ≤ t), Φ t '' C with hΛ
  have hΛE : (⋂ t : ℝ, ⋂ (_ : 0 ≤ t), Φ t '' E) = Λ := by
    apply Subset.antisymm
    · exact iInter₂_mono fun t _ => image_mono subset_closure
    · intro y hy
      simp only [hΛ, mem_iInter] at hy ⊢
      intro t ht
      obtain ⟨w, hw, rfl⟩ := hy (t + 1) (by linarith)
      exact ⟨Φ 1 w, (hEtrap w hw 1 one_pos).2, by rw [hcomp w hw 1 t zero_le_one ht]⟩
  have hω : omegaPlusSet M I Φ E = Λ := by
    apply Subset.antisymm
    · rintro y ⟨-, t, x, hx, ht, hlim⟩
      simp only [hΛ, mem_iInter]
      intro s hs
      have hev : ∀ᶠ k in atTop, s ≤ t k := ht.eventually (eventually_ge_atTop s)
      set z : ℕ → EuclideanSpace ℝ (Fin n) := fun k => Φ (t k - s) (x k) with hz
      have hzE : ∀ᶠ k in atTop, z k ∈ C ∧ Φ s (z k) = Φ (t k) (x k) := by
        filter_upwards [hev] with k hk
        have hxk : x k ∈ C := subset_closure (hx k).1
        refine ⟨hstay _ hxk _ (by linarith), ?_⟩
        have := hcomp (x k) hxk (t k - s) s (by linarith) hs
        rw [hz]; simpa using this
      obtain ⟨w, hw, φ, hφ, hzφ⟩ := hEc.tendsto_subseq' (hzE.mono fun k hk => hk.1).frequently
      have hzEφ := hφ.tendsto_atTop.eventually hzE
      have h1 : Tendsto (fun k => Φ s (z (φ k))) atTop (𝓝 (Φ s w)) := by
        have hw' : Tendsto (z ∘ φ) atTop (𝓝[C] w) :=
          tendsto_nhdsWithin_iff.mpr ⟨hzφ, hzEφ.mono fun k hk => hk.1⟩
        exact ((hcont s hs) w hw).tendsto.comp hw'
      have h2 : Tendsto (fun k => Φ s (z (φ k))) atTop (𝓝 y) := by
        refine (hlim.comp hφ.tendsto_atTop).congr' ?_
        filter_upwards [hzEφ] with k hk
        exact hk.2.symm
      exact ⟨w, hw, tendsto_nhds_unique h1 h2⟩
    · intro y hy
      simp only [hΛ, mem_iInter] at hy
      have hyC : y ∈ C := by
        obtain ⟨w, hw, rfl⟩ := hy 0 le_rfl
        rw [hid w hw]; exact hw
      have hk : ∀ k : ℕ, ∃ w ∈ C, Φ ((k : ℝ) + 1) w = y := fun k =>
        hy _ (by positivity)
      choose w hw hwy using hk
      refine ⟨hEM hyC, fun k => (k : ℝ), fun k => Φ 1 (w k), fun k => ⟨(hEtrap _ (hw k) 1 one_pos).2,
        hnn _ (subset_closure (hEtrap _ (hw k) 1 one_pos).2) _ (Nat.cast_nonneg k)⟩,
        tendsto_natCast_atTop_atTop, ?_⟩
      refine tendsto_const_nhds.congr fun k => ?_
      rw [hcomp (w k) (hw k) 1 k zero_le_one (Nat.cast_nonneg k), hwy k]
  have hΛC : Λ ⊆ C := by
    intro y hy
    simp only [hΛ, mem_iInter] at hy
    obtain ⟨w, hw, rfl⟩ := hy 0 le_rfl
    rw [hid w hw]; exact hw
  have hΛsubE : Λ ⊆ E := by
    intro y hy
    simp only [hΛ, mem_iInter] at hy
    obtain ⟨w, hw, rfl⟩ := hy 1 zero_le_one
    exact (hEtrap w hw 1 one_pos).2
  have hVc : ∀ t : ℝ, 0 ≤ t → IsCompact (Φ t '' C) := fun t ht =>
    hEc.image_of_continuousOn (hcont t ht)
  have hΛclosed : IsClosed Λ := isClosed_iInter fun t => isClosed_iInter fun ht => (hVc t ht).isClosed
  have hΛcpt : IsCompact Λ := hEc.of_isClosed_subset hΛclosed hΛC
  -- nonempty
  have hne : Λ.Nonempty := by
    obtain ⟨e, he⟩ := hEconn.nonempty
    have heC : e ∈ C := subset_closure he
    obtain ⟨y, hyC, φ, hφ, hlim⟩ := hEc.tendsto_subseq
      (x := fun k : ℕ => Φ (k : ℝ) e) fun k => hstay e heC _ (Nat.cast_nonneg k)
    refine ⟨y, ?_⟩
    rw [← hω]
    refine ⟨hEM hyC, fun k => ((φ k : ℕ) : ℝ), fun _ => e, fun k => ⟨he, hnn e heC _ (Nat.cast_nonneg _)⟩,
      tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop, hlim⟩
  -- invariance
  have hinv : IsInvariant M I Φ Λ := by
    refine ⟨fun y hy => hEM (hΛC hy), fun x hx t ht => ?_⟩
    have hx' := hx
    simp only [hΛ, mem_iInter] at hx ⊢
    intro s hs
    rcases le_or_gt 0 t with h0 | h0
    · obtain ⟨w, hw, rfl⟩ := hx s hs
      refine ⟨Φ t w, hstay w hw t h0, ?_⟩
      rw [hcomp w hw t s h0 hs, hcomp w hw s t hs h0, add_comm]
    · obtain ⟨w, hw, rfl⟩ := hx (s - t) (by linarith)
      refine ⟨w, hw, ?_⟩
      have := (flow_core f M I Φ hΦ w (hEM hw) (s - t) (hnn w hw _ (by linarith)) t
        (by simpa using hnn w hw s hs)).2
      rw [this]; ring_nf
  -- connectedness
  have hconn : IsConnected Λ := by
    refine ⟨hne, (isPreconnected_iff_subset_of_fully_disjoint_closed hΛclosed).mpr ?_⟩
    intro u v hu hv hsub huv
    obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
      (hΛcpt.inter_right hu) (hΛcpt.inter_right hv)
      (disjoint_of_subset inter_subset_right inter_subset_right huv)
    have hΛUV : Λ ⊆ U ∪ V := by
      intro y hy
      rcases hsub hy with h | h
      · exact Or.inl (hAU ⟨hy, h⟩)
      · exact Or.inr (hBV ⟨hy, h⟩)
    have hdir : Directed (· ⊇ ·) (fun t : {t : ℝ // 0 ≤ t} => Φ t.1 '' C) := by
      intro i j
      refine ⟨⟨max i.1 j.1, le_trans i.2 (le_max_left _ _)⟩, ?_, ?_⟩
      · rintro y ⟨w, hw, rfl⟩
        refine ⟨Φ (max i.1 j.1 - i.1) w, hstay w hw _ (by linarith [le_max_left i.1 j.1]), ?_⟩
        rw [hcomp w hw _ _ (by linarith [le_max_left i.1 j.1]) i.2]; ring_nf
      · rintro y ⟨w, hw, rfl⟩
        refine ⟨Φ (max i.1 j.1 - j.1) w, hstay w hw _ (by linarith [le_max_right i.1 j.1]), ?_⟩
        rw [hcomp w hw _ _ (by linarith [le_max_right i.1 j.1]) j.2]; ring_nf
    obtain ⟨⟨t, ht⟩, hT⟩ := exists_subset_nhds_of_isCompact (ι := {t : ℝ // 0 ≤ t})
      (V := fun t => Φ t.1 '' C)
      hdir
      (fun i => hVc i.1 i.2)
      (U := U ∪ V) (fun y hy => (hUo.union hVo).mem_nhds (hΛUV (by
        simp only [hΛ, mem_iInter]
        intro t ht
        exact (mem_iInter.mp hy) ⟨t, ht⟩)))
    have hVt : IsPreconnected (Φ t '' C) :=
      (hEconn.isPreconnected.closure).image _ (hcont t ht)
    have hΛV : Λ ⊆ Φ t '' C := fun y hy => by
      simp only [hΛ, mem_iInter] at hy; exact hy t ht
    by_cases hU : (Φ t '' C ∩ U).Nonempty
    · left
      have hsU := hVt.subset_left_of_subset_union hUo hVo hUV hT hU
      intro y hy
      rcases hsub hy with h | h
      · exact h
      · exact absurd (hBV ⟨hy, h⟩) (Set.disjoint_left.mp hUV (hsU (hΛV hy)))
    · right
      intro y hy
      rcases hsub hy with h | h
      · exact absurd ⟨hΛV hy, hAU ⟨hy, h⟩⟩ (fun h' => hU ⟨y, h'⟩)
      · exact h
  -- attracting
  have hattr : stableSet M I Φ 1 Λ ∈ nhdsSet Λ := by
    rw [mem_nhdsSet_iff_exists]
    refine ⟨E, hEo, hΛsubE, fun x hx => ⟨hEM (subset_closure hx), fun t ht => hnn x (subset_closure hx) t
      (by simpa using ht), ?_⟩⟩
    have hxC : x ∈ C := subset_closure hx
    by_contra hnot
    obtain ⟨u, hu, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hnot
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu
    have hseq : ∀ k : ℕ, ∃ s : ℝ, (k : ℝ) ≤ s ∧
        Metric.infDist (Φ (1 * s) x) Λ ∉ u := fun k => (frequently_atTop.mp hfreq) k
    choose s hsk hsu using hseq
    have hs0 : ∀ k, 0 ≤ s k := fun k => le_trans (Nat.cast_nonneg k) (hsk k)
    obtain ⟨y, hyC, φ, hφ, hlim⟩ := hEc.tendsto_subseq
      (x := fun k => Φ (s k) x) fun k => hstay x hxC _ (hs0 k)
    have hyΛ : y ∈ Λ := by
      rw [← hω]
      refine ⟨hEM hyC, fun k => s (φ k), fun _ => x, fun k => ⟨hx, hnn x hxC _ (hs0 _)⟩, ?_, hlim⟩
      exact tendsto_atTop_mono (fun k => le_trans (Nat.cast_le.mpr (hφ.id_le k)) (hsk (φ k)))
        tendsto_natCast_atTop_atTop
    have hd : Tendsto (fun k => Metric.infDist (Φ (s (φ k)) x) Λ) atTop (𝓝 (Metric.infDist y Λ)) :=
      ((Metric.continuous_infDist_pt Λ).tendsto y).comp hlim
    rw [Metric.infDist_zero_of_mem hyΛ] at hd
    obtain ⟨k, hk⟩ := (hd.eventually (Metric.ball_mem_nhds 0 hε)).exists
    exact hsu (φ k) (hball (by simpa using hk))
  rw [hΛE, hω]
  exact ⟨rfl, hne, hinv, hΛcpt, hconn, hinv, hattr⟩

#print axioms solution
