-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_param_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:51.226723+00:00
-- url     : https://prove2.me/submissions/67053931-2a27-40b0-b145-accdc0e651bb

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_analyticAt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_insertNth_eq
import Theorems.Thm_ReciprocityTheory_AnForm_exists_analytic_graph_chart_mvPolynomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {D c : ℕ} (Z : Set (Fin (D + 1 + c) → ℂ))
    (hZc : ∀ z ∈ Z, ∀ t : ℂ, t ≠ 0 → t • z ∈ Z)
    (F : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ) (h : MvPolynomial (Fin (D + 1 + c)) ℂ)
    (hZ : ∀ z, z ≠ 0 → eval z h ≠ 0 → (z ∈ Z ↔ ∀ i, eval z (F i) = 0))
    (p : Fin (D + 1 + c) → ℂ) (hp : p ∈ Z) (hp0 : p ≠ 0) (hph : eval p h ≠ 0)
    (hjac : Function.Surjective (fun v : Fin (D + 1 + c) → ℂ =>
      fun i => ∑ j, eval p (pderiv j (F i)) * v j)) :
    ∃ (ρ₀ : ℝ) (γ : (Fin D → ℂ) → Fin (D + 1 + c) → ℂ), 0 < ρ₀ ∧
      AnalyticOnNhd ℂ γ (Metric.ball 0 ρ₀) ∧ (∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, γ y ∈ Z) ∧
      (∃ (O : Set (Fin (D + 1 + c) → ℂ)) (q : (Fin (D + 1 + c) → ℂ) → Fin D → ℂ), IsOpen O ∧
        AnalyticOnNhd ℂ q O ∧ O ∩ Z = coneOver (Metric.ball 0 ρ₀) γ ∧
        (∀ z ∈ O, ∀ t : ℂ, t ≠ 0 → t • z ∈ O ∧ q (t • z) = q z) ∧
        ∀ y ∈ Metric.ball 0 ρ₀, q (γ y) = y) ∧ γ 0 = p := by
  classical
  have hF0 : ∀ i, eval p (F i) = 0 := (hZ p hp0 hph).1 hp
  obtain ⟨σ, U, V, g, hU, hpU, hV, hg, hbij, hproj⟩ :=
    ReciprocityTheory.AnForm.exists_analytic_graph_chart_mvPolynomial F p hF0 hjac
  obtain ⟨π, hπ⟩ : ∃ π : (Fin (D + 1 + c) → ℂ) → Fin (D + 1) → ℂ,
      π = fun z i => z (σ (Fin.castAdd c i)) := ⟨_, rfl⟩
  have hπa : ∀ z i, π z i = z (σ (Fin.castAdd c i)) := fun z i => by rw [hπ]
  have hπs : ∀ (t : ℂ) z, π (t • z) = t • π z := fun t z => by
    funext i
    simp [hπa]
  have hπg : ∀ w ∈ V, π (g w) = w := fun w hw => by
    rw [hπ]
    exact hproj w hw
  have hπan : ∀ j z, AnalyticAt ℂ (fun z => π z j) z := fun j z => by
    rw [hπ]
    exact gbap_analyticAt_apply _ z
  have htgt : ∀ z, z ≠ 0 → z ∈ Z → z ∈ U → eval z h ≠ 0 → ∃ w ∈ V, g w = z ∧ w = π z := by
    intro z hz0 hzZ hzU hzh
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hzU, (hZ z hz0 hzh).1 hzZ⟩
    exact ⟨w, hw, hgw, by rw [← hgw, hπg w hw]⟩
  obtain ⟨w₀, hw₀V, hgw₀, hw₀⟩ := htgt p hp0 hp hpU hph
  have hπp : π p ≠ 0 := by
    intro hπ0
    have hWo : IsOpen (U ∩ {z | eval z h ≠ 0} ∩ {z | z ≠ 0}) :=
      (hU.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)).inter
        isOpen_ne
    have hc : ContinuousAt (fun t : ℂ => t • p) 1 :=
      (continuous_id.smul continuous_const).continuousAt
    have hev : ∀ᶠ t in nhds (1 : ℂ), t • p ∈ U ∩ {z | eval z h ≠ 0} ∩ {z | z ≠ 0} :=
      hc.preimage_mem_nhds (by rw [one_smul]; exact hWo.mem_nhds ⟨⟨hpU, hph⟩, hp0⟩)
    obtain ⟨t, ⟨⟨htU, hth⟩, htp0⟩, ht1⟩ :=
      ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := ({1}ᶜ : Set ℂ)))).exists
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact htp0 (zero_smul ℂ p)
    obtain ⟨w, hwV, hgw, hw⟩ := htgt (t • p) htp0 (hZc p hp t ht0) htU hth
    have hw0 : w = w₀ := by
      rw [hw, hw₀, hπs, hπ0, smul_zero]
    have htp : t • p = p := by rw [← hgw, hw0, hgw₀]
    have : (t - 1) • p = 0 := by rw [sub_smul, one_smul, htp, sub_self]
    rcases smul_eq_zero.1 this with h1 | h1
    · exact ht1 (sub_eq_zero.1 h1)
    · exact hp0 h1
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hπp
  set a := π p k with ha_def
  have ha : a ≠ 0 := hk
  obtain ⟨W, hW⟩ : ∃ W : (Fin D → ℂ) → Fin (D + 1) → ℂ,
      W = fun y => Fin.insertNth k a (fun i => π p (k.succAbove i) + y i) := ⟨_, rfl⟩
  have hWk : ∀ y, W y k = a := fun y => by rw [hW]; simp
  have hWs : ∀ y i, W y (k.succAbove i) = π p (k.succAbove i) + y i := fun y i => by
    rw [hW]; simp
  have hW0 : W 0 = π p := by
    rw [hW]
    exact gbap_insertNth_eq k a _ (π p) rfl (fun i => by simp)
  have hWan : ∀ y, AnalyticAt ℂ W y := by
    intro y
    rw [hW]
    refine analyticAt_pi_iff.2 fun j => ?_
    rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
    · simp only [Fin.insertNth_apply_same]
      exact analyticAt_const
    · simp only [Fin.insertNth_apply_succAbove]
      exact analyticAt_const.add (gbap_analyticAt_apply i y)
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun y => (hWan y).continuousAt
  have hGo : IsOpen (V ∩ g ⁻¹' {z | eval z h ≠ 0}) :=
    hg.continuousOn.isOpen_inter_preimage hV
      (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)
  have h0G : (0 : Fin D → ℂ) ∈ W ⁻¹' (V ∩ g ⁻¹' {z | eval z h ≠ 0}) := by
    simp only [Set.mem_preimage, Set.mem_inter_iff, hW0, ← hw₀]
    exact ⟨hw₀V, by rw [Set.mem_ofPred_eq, hgw₀]; exact hph⟩
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 (hGo.preimage hWc) 0 h0G
  have hyV : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, W y ∈ V ∧ eval (g (W y)) h ≠ 0 :=
    fun y hy => hball hy
  have hγmem : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀,
      g (W y) ∈ U ∧ ∀ i, eval (g (W y)) (F i) = 0 := fun y hy => hbij.mapsTo (hyV y hy).1
  have hπγ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, π (g (W y)) = W y := fun y hy =>
    hπg _ (hyV y hy).1
  have hγ0 : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, g (W y) ≠ 0 := by
    intro y hy h0
    have := congrFun (hπγ y hy) k
    rw [h0, hWk, hπa] at this
    exact ha (by simpa using this.symm)
  have hγZ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, g (W y) ∈ Z := fun y hy =>
    (hZ _ (hγ0 y hy) (hyV y hy).2).2 (hγmem y hy).2
  obtain ⟨q, hq⟩ : ∃ q : (Fin (D + 1 + c) → ℂ) → Fin D → ℂ,
      q = fun z i => π z (k.succAbove i) * a / π z k - π p (k.succAbove i) := ⟨_, rfl⟩
  have hqa : ∀ z i, q z i = π z (k.succAbove i) * a / π z k - π p (k.succAbove i) :=
    fun z i => by rw [hq]
  obtain ⟨ν, hν⟩ : ∃ ν : (Fin (D + 1 + c) → ℂ) → Fin (D + 1 + c) → ℂ,
      ν = fun z => (a / π z k) • z := ⟨_, rfl⟩
  have hνa : ∀ z, ν z = (a / π z k) • z := fun z => by rw [hν]
  set A : Set (Fin (D + 1 + c) → ℂ) := {z | π z k ≠ 0} with hA
  have hAo : IsOpen A :=
    isOpen_ne_fun (continuous_iff_continuousAt.2 fun z => (hπan k z).continuousAt) continuous_const
  have hqan : ∀ z ∈ A, AnalyticAt ℂ q z := by
    intro z hz
    rw [hq]
    refine analyticAt_pi_iff.2 fun i => ?_
    exact (((hπan _ z).mul analyticAt_const).div (hπan k z) hz).sub analyticAt_const
  have hνan : ∀ z ∈ A, AnalyticAt ℂ ν z := by
    intro z hz
    rw [hν]
    refine analyticAt_pi_iff.2 fun j => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (analyticAt_const.div (hπan k z) hz).mul (gbap_analyticAt_apply j z)
  set O : Set (Fin (D + 1 + c) → ℂ) :=
    A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0}) ∩ q ⁻¹' Metric.ball 0 ρ₀ with hO
  have hOo : IsOpen O := by
    have h1 : IsOpen (A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0})) :=
      ContinuousOn.isOpen_inter_preimage (show ContinuousOn ν A from fun z hz => (hνan z hz).continuousAt.continuousWithinAt)
        hAo (hU.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const))
    exact ContinuousOn.isOpen_inter_preimage (show ContinuousOn q (A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0})) from
      fun z hz => (hqan z hz.1).continuousAt.continuousWithinAt) h1
      Metric.isOpen_ball
  have hπks : ∀ z (t : ℂ), π (t • z) k = t * π z k := fun z t => by rw [hπs]; rfl
  have hνs : ∀ z (t : ℂ), t ≠ 0 → π z k ≠ 0 → ν (t • z) = ν z := by
    intro z t ht hz
    rw [hνa, hνa, hπks, smul_smul]
    congr 1
    field_simp
  have hqs : ∀ z (t : ℂ), t ≠ 0 → π z k ≠ 0 → q (t • z) = q z := by
    intro z t ht hz
    funext i
    rw [hqa, hqa, hπs]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  have hqγ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, q (g (W y)) = y := by
    intro y hy
    funext i
    rw [hqa, hπγ y hy, hWk, hWs]
    field_simp
    ring
  refine ⟨ρ₀, fun y => g (W y), hρ₀, ?_, hγZ, ⟨O, q, hOo, fun z hz => hqan z hz.1.1, ?_, ?_, hqγ⟩, ?_⟩
  · intro y hy
    exact (hg _ (hyV y hy).1).comp (hWan y)
  · ext z
    constructor
    · rintro ⟨⟨⟨hzA, hzU, hzh⟩, hzq⟩, hzZ⟩
      have hzA' : π z k ≠ 0 := hzA
      have hc : a / π z k ≠ 0 := div_ne_zero ha hzA'
      have hνZ : ν z ∈ Z := by rw [hνa]; exact hZc z hzZ _ hc
      have hν0 : ν z ≠ 0 := by
        intro h0
        have := hπks z (a / π z k)
        rw [← hνa, h0] at this
        rw [hπa] at this
        simp only [Pi.zero_apply] at this
        field_simp at this
        exact ha this.symm
      obtain ⟨w, hwV, hgw, hw⟩ := htgt (ν z) hν0 hνZ hzU hzh
      have hWq : W (q z) = π (ν z) := by
        rw [hW]
        apply gbap_insertNth_eq
        · rw [hνa, hπks]
          field_simp
        · intro i
          rw [hνa, hπs, hqa]
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
      refine ⟨q z, hzq, π z k / a, div_ne_zero hzA' ha, ?_⟩
      simp only
      rw [hWq, ← hw, hgw, hνa, smul_smul]
      rw [div_mul_div_comm, mul_comm (π z k) a, div_self (mul_ne_zero ha hzA'), one_smul]
    · rintro ⟨y, hy, t, ht, rfl⟩
      have hwk : π (g (W y)) k = a := by rw [hπγ y hy, hWk]
      have hwk0 : π (g (W y)) k ≠ 0 := by rw [hwk]; exact ha
      have hνw : ν (t • g (W y)) = g (W y) := by
        rw [hνs _ _ ht hwk0, hνa, hwk, div_self ha, one_smul]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hZc _ (hγZ y hy) t ht⟩
      · show π (t • g (W y)) k ≠ 0
        rw [hπks]
        exact mul_ne_zero ht hwk0
      · simp only [Set.mem_preimage, hνw]
        exact ⟨(hγmem y hy).1, (hyV y hy).2⟩
      · simp only [Set.mem_preimage]
        rw [hqs _ _ ht hwk0, hqγ y hy]
        exact hy
  · intro z hz t ht
    have hzA : π z k ≠ 0 := hz.1.1
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hqs z t ht hzA⟩
    · show π (t • z) k ≠ 0
      rw [hπks]
      exact mul_ne_zero ht hzA
    · simp only [Set.mem_preimage]
      rw [hνs z t ht hzA]
      exact hz.1.2
    · simp only [Set.mem_preimage]
      rw [hqs z t ht hzA]
      exact hz.2
  · simp only
    rw [hW0, ← hw₀, hgw₀]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
