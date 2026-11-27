-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BranchAwayFromRim_proof_8e0b4e2d65cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:27.683156+00:00
-- url     : https://prove2.me/submissions/bbceeef0-5e49-4cb4-81cb-f7cb51437518

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchAwayFromRim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchContainsNormalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchAwayFromRim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace BranchAwayFromRim
theorem _root_.solution (hex : NormalModelExists.Statement)
    (hprop : NormalModelProper.Statement) (hlift : BranchLift.Statement)
    (hirr : NormalLocallyIrreducible.Statement) (hext : BranchContainsNormalPoint.Statement) :
    BranchAwayFromRim.Statement := by
  intro n k J u p x m γ hJ hdim hu hcov hdisj b
  obtain ⟨N, hN, hcovN⟩ := hcov
  obtain ⟨M⟩ := hex n J hJ
  set Z' := zeroSetIn M.ideal with hZ'
  have hcontν : Continuous (firstCoords : (Fin n ⊕ Fin M.m → ℂ) → Fin n → ℂ) :=
    continuous_pi fun i => continuous_apply _
  have hZc : IsClosed Z' := by
    have hZ'eq : Z' = ⋂ q ∈ M.ideal, {z | eval z q = 0} := by ext z; simp [Z', zeroSetIn]
    rw [hZ'eq]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hνZ : ∀ w ∈ Z', firstCoords w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J := by
    intro w hw q hq
    have hq' : rename Sum.inl q ∈ M.ideal := by rw [← M.comap_eq] at hq; exact hq
    have := hw _ hq'
    rwa [eval_rename] at this

  choose Γ hΓd hΓZ hΓopen using fun c => hlift n k J p M (γ c) hJ hdim
  have hΓinj : ∀ c, Set.InjOn (Γ c) (Metric.ball 0 (γ c).radius) := by
    intro c s hs t ht hst
    apply (γ c).injOn hs ht
    rw [← (hΓZ c s hs).2, ← (hΓZ c t ht).2, hst]
  choose O hOo hOeq using fun c => hΓopen c (Metric.ball 0 (γ c).radius) subset_rfl Metric.isOpen_ball

  choose a bd hbJ hab using M.birational
  set g : MvPolynomial (Fin n) ℂ := GroundTheory.Heights₂.Heights.linForm u * ∏ i, bd i with hg
  have hgJ : g ∉ J := by
    have := hJ
    intro hgm
    rcases hJ.mem_or_mem hgm with h1 | h2
    · exact hu h1
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h2
      exact hbJ i hi
  set h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl g with hh_def
  have hh : h ∉ M.ideal := by
    intro hm
    apply hgJ
    rw [← M.comap_eq]
    exact hm
  have heval : ∀ w : Fin n ⊕ Fin M.m → ℂ,
      eval w h = GroundTheory.Heights₂.Heights.linEval u (firstCoords w) *
        ∏ i, eval (firstCoords w) (bd i) := by
    intro w
    simp only [h, g, eval_rename, map_mul, map_prod]
    congr 1
    simp [GroundTheory.Heights₂.Heights.linForm, GroundTheory.Heights₂.Heights.linEval, firstCoords, Function.comp_def]
  have hinj : ∀ w ∈ Z', ∀ w' ∈ Z', firstCoords w = firstCoords w' → eval w h ≠ 0 → w = w' := by
    intro w hw w' hw' hνw hne
    rw [heval] at hne
    have hb : ∀ i, eval (firstCoords w) (bd i) ≠ 0 := fun i hi =>
      hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero])
    funext s
    rcases s with j | i
    · exact congrFun hνw j
    · have e1 := hw _ (hab i)
      have e2 := hw' _ (hab i)
      simp only [map_sub, map_mul, eval_rename, eval_X] at e1 e2
      have c1 : w ∘ Sum.inl = firstCoords w := rfl
      have c2 : w' ∘ Sum.inl = firstCoords w := by rw [hνw]; rfl
      rw [c1] at e1
      rw [c2] at e2
      apply mul_left_cancel₀ (hb i)
      linear_combination e1 - e2

  by_contra hcon
  push Not at hcon
  set r := (γ b).radius with hr
  have hseq : ∀ j : ℕ, ∃ τ ∈ Metric.ball (0 : Fin k → ℂ) r,
      (γ b).toFun τ ∈ Metric.ball x (1 / ((j : ℝ) + 1)) ∧ r - 1 / ((j : ℝ) + 1) < ‖τ‖ := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    exact hcon _ hpos _ (by linarith)
  choose τ hτr hτx hτn using hseq
  have hmem : ∀ j, Γ b (τ j) ∈ {w | w ∈ Z' ∧ firstCoords w ∈ Metric.closedBall x 1} := by
    intro j
    refine ⟨(hΓZ b (τ j) (hτr j)).1, ?_⟩
    rw [(hΓZ b (τ j) (hτr j)).2, Metric.mem_closedBall]
    have h1 := Metric.mem_ball.mp (hτx j)
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith
  obtain ⟨xh, hxcl, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (hprop n J M _ Metric.isBounded_closedBall) hmem
  have hlim' : Tendsto (fun j => Γ b (τ (φ j))) atTop (𝓝 xh) := hlim
  have hxZ : xh ∈ Z' := hZc.closure_subset_iff.mpr (fun w hw => hw.1) hxcl
  have h1j : Tendsto (fun j => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hγlim : Tendsto (fun j => (γ b).toFun (τ (φ j))) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun j => dist_nonneg) (fun j => (Metric.mem_ball.mp (hτx (φ j))).le) h1j
  have hνx : firstCoords xh = x := by
    refine tendsto_nhds_unique ((hcontν.tendsto xh).comp hlim') ?_
    refine hγlim.congr fun j => ?_
    exact ((hΓZ b _ (hτr _)).2).symm

  have hUN : firstCoords ⁻¹' N ∈ 𝓝 xh :=
    hcontν.continuousAt.preimage_mem_nhds (by rw [hνx]; exact hN)
  obtain ⟨B, hBo, hxB, hBU, hpre, hdense⟩ :=
    hirr (Fin n ⊕ Fin M.m) M.ideal h xh M.isPrime M.isIntegrallyClosed hh hxZ _ hUN
  set P := (Z' ∩ B) \ {z | eval z h = 0} with hP

  have hPcov : ∀ q ∈ P, ∃ c, q ∈ Γ c '' Metric.ball 0 (γ c).radius := by
    rintro q ⟨⟨hqZ, hqB⟩, hqh⟩
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcovN ⟨hνZ q hqZ, hBU hqB⟩)
    obtain ⟨t, ht, hteq⟩ := hc
    refine ⟨c, t, ht, ?_⟩
    have hν : firstCoords (Γ c t) = firstCoords q := by rw [(hΓZ c t ht).2, hteq]
    refine hinj _ (hΓZ c t ht).1 q hqZ hν ?_
    rw [heval, hν, ← heval]
    exact hqh
  have hPdisj : ∀ q ∈ P, ∀ c c', c ≠ c' → q ∈ Γ c '' Metric.ball 0 (γ c).radius →
      q ∉ Γ c' '' Metric.ball 0 (γ c').radius := by
    rintro q ⟨-, hqh⟩ c c' hcc' ⟨t, ht, rfl⟩ ⟨t', ht', hteq⟩
    have h1 : firstCoords (Γ c t) ∈ (γ c).image := ⟨t, ht, ((hΓZ c t ht).2).symm⟩
    have h2 : firstCoords (Γ c t) ∈ (γ c').image :=
      ⟨t', ht', by rw [← (hΓZ c' t' ht').2, hteq]⟩
    have h3 := hdisj c c' hcc' ⟨h1, h2⟩
    apply hqh
    show eval (Γ c t) h = 0
    rw [heval]
    rw [show GroundTheory.Heights₂.Heights.linEval u (firstCoords (Γ c t)) = 0 from h3, zero_mul]

  have hPsub : P ⊆ Γ b '' Metric.ball 0 r := by
    have hsplit := isPreconnected_iff_subset_of_disjoint.mp hpre (O b) (⋃ c ∈ {c | c ≠ b}, O c)
      (hOo b) (isOpen_biUnion fun c _ => hOo c) ?_ ?_
    · rcases hsplit with hs | hs
      · intro q hq
        rw [hOeq b]
        exact ⟨hq.1.1, hs hq⟩
      · exfalso
        obtain ⟨j, hjB⟩ := (hlim'.eventually (hBo.mem_nhds hxB)).exists
        have hw0 : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball 0 r := ⟨_, hτr _, rfl⟩
        have hw0O : Γ b (τ (φ j)) ∈ O b := by
          have := hw0
          rw [hOeq b] at this
          exact this.2
        have hw0P := hdense ⟨(hΓZ b _ (hτr _)).1, hjB⟩
        obtain ⟨q, hqO, hqP⟩ := mem_closure_iff.mp hw0P (O b) (hOo b) hw0O
        obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp (hs hqP)
        have hqb : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqO⟩
        have hqc' : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
        exact hPdisj q hqP b c (Ne.symm hc) hqb hqc'
    · intro q hq
      obtain ⟨c, hc⟩ := hPcov q hq
      rw [hOeq c] at hc
      by_cases hcb : c = b
      · subst hcb
        exact Or.inl hc.2
      · exact Or.inr (Set.mem_biUnion hcb hc.2)
    · ext q
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hqP hqb hqv
      obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp hqv
      have h1 : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqb⟩
      have h2 : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
      exact hPdisj q hqP b c (Ne.symm hc) h1 h2

  obtain ⟨σ0, hσ0, hσx⟩ := hext (Fin n ⊕ Fin M.m) M.ideal h xh k r (Γ b) B M.isPrime
    M.isIntegrallyClosed hh hxZ (hΓd b) (hΓinj b) (fun t ht => (hΓZ b t ht).1)
    (hBo.mem_nhds hxB) hPsub

  have hσ0' : ‖σ0‖ < r := mem_ball_zero_iff.mp hσ0
  set δ := (r - ‖σ0‖) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hVsub : Metric.ball σ0 δ ⊆ Metric.ball 0 r := by
    intro t ht
    rw [mem_ball_zero_iff]
    have h1 : ‖t‖ ≤ ‖σ0‖ + dist t σ0 := by
      rw [dist_eq_norm]
      calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
        _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
    have h2 := Metric.mem_ball.mp ht
    linarith
  obtain ⟨O', hO'o, hO'eq⟩ := hΓopen b (Metric.ball σ0 δ) hVsub Metric.isOpen_ball
  have hxO' : xh ∈ O' := by
    have : xh ∈ Γ b '' Metric.ball σ0 δ := ⟨σ0, Metric.mem_ball_self hδpos, hσx⟩
    rw [hO'eq] at this
    exact this.2
  obtain ⟨j, hjO, hjδ⟩ :=
    ((hlim'.eventually (hO'o.mem_nhds hxO')).and (h1j.eventually (gt_mem_nhds hδpos))).exists
  have hjV : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball σ0 δ := by
    rw [hO'eq]
    exact ⟨(hΓZ b _ (hτr _)).1, hjO⟩
  obtain ⟨t, ht, hteq⟩ := hjV
  have htτ : t = τ (φ j) := hΓinj b (hVsub ht) (hτr _) hteq
  have hn1 : ‖τ (φ j)‖ < ‖σ0‖ + δ := by
    rw [← htτ]
    have h2 := Metric.mem_ball.mp ht
    rw [dist_eq_norm] at h2
    calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
      _ < ‖σ0‖ + δ := by linarith
  have hn2 := hτn (φ j)
  linarith
end BranchAwayFromRim
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
