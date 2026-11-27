-- Prove2me | solution 1 for RetirePartialInfo.Duality.Supplement.theorem_3_1_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:25.811743+00:00
-- url     : https://prove2.me/submissions/23d35d3c-cd38-40b7-b780-80b52ef88c91

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Supplement_Analysis

open Set Filter MeasureTheory
open scoped Topology
set_option autoImplicit false

open RetirePartialInfo
open RetirePartialInfo.Duality
open RetirePartialInfo.Duality.Supplement

/-- Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553
(version of June 8, 2021), p.19, Theorem 3.1; p.17, (30); pp.35–36, Appendix A.
**Formalization Note.** Counterexample to the printed global claim, not a local replacement.
For γ>1 the terminal conjugate is negative. Continuity near the terminal face and the
claimed negative y derivative force a negative lower bound on |v| on an infinite-y slab,
contradicting even its zeroth-order global L^q term. The remaining clauses of the original
claim are retained inside the negated package. The working counterexample has T=T1=1,
r=σ=β=ℓ=1, ξ=0, μ1=2, μ2=0, rate1=rate2=1, γ=2. -/
theorem solution (a : Data) (ha : a.Admissible) (hg : 1 < a.γ)
    (q : ℝ) (hq : 1 ≤ q) :
    ¬ ∃ v : Value,
      GlobalW a.par.T q v ∧ PDE30 a v ∧ C122 a.par.T v ∧
      (∀ z ∈ domain a.par.T, 0 < dyy v (z 0) (z 1) (z 2) ∧
        dy v (z 0) (z 1) (z 2) < 0) ∧
      (∀ t ∈ Ico (0 : ℝ) a.par.T, ∀ p ∈ Ioo (0 : ℝ) 1,
        Tendsto (fun y => dy v t y p) (𝓝[>] 0) atBot ∧
        Tendsto (fun y => dy v t y p) atTop (𝓝[<] 0)) ∧
      Growth a.par.T v := by
        rintro ⟨v, hW, hPDE, hC, hsign, _hlim, _hgr⟩
        have hT := a.par.T_pos
        have hγ1 : 1 - a.γ < 0 := by linarith
        set m : ℝ := max (1 / (1 - a.γ)) (-1) with hm
        have hm0 : m < 0 := max_lt (div_neg_of_pos_of_neg one_pos hγ1) (by norm_num)
        have hUt : ∀ y : ℝ, 1 ≤ y → Utilde (crra a) a.par.T y ≤ m := by
          intro y hy
          unfold Utilde
          apply csSup_le
          · exact ⟨_, ⟨1, by norm_num, rfl⟩⟩
          · rintro _ ⟨c, hc, rfl⟩
            have hc' : 0 < c := hc
            simp only [crra]
            rcases le_total c 1 with h | h
            · have h1 : 1 ≤ c ^ (1 - a.γ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc' h hγ1.le
              have h2 : c ^ (1 - a.γ) / (1 - a.γ) ≤ 1 / (1 - a.γ) := div_le_div_of_nonpos_of_le hγ1.le h1
              have h3 : 0 ≤ y * c := by positivity
              exact le_max_of_le_left (by linarith)
            · have h1 : c ^ (1 - a.γ) / (1 - a.γ) ≤ 0 :=
                div_nonpos_of_nonneg_of_nonpos (by positivity) hγ1.le
              have h3 : 1 ≤ y * c := by nlinarith
              exact le_max_of_le_right (by linarith)
        -- monotonicity in y
        have hanti : ∀ t ∈ Ico (0 : ℝ) a.par.T, ∀ p ∈ Ioo (0 : ℝ) 1,
            AntitoneOn (fun y => v t y p) (Ioi 0) := by
          intro t ht p hp
          have hneg : ∀ y : ℝ, 0 < y → dy v t y p < 0 := by
            intro y hy
            have := (hsign (state t y p) (by simp [domain, state]; exact ⟨ht, hy, hp⟩)).2
            simpa [state] using this
          have hdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (fun z => v t z p) y := by
            intro y hy
            by_contra hnd
            have := hneg y hy
            simp only [dy] at this
            rw [deriv_zero_of_not_differentiableAt hnd] at this
            exact lt_irrefl _ this
          apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
          · exact fun y hy => (hdiff y hy).continuousAt.continuousWithinAt
          · rw [interior_Ioi]; exact fun y hy => (hdiff y hy).differentiableWithinAt
          · rw [interior_Ioi]; exact fun y hy => (hneg y hy).le
        -- continuity at the terminal point
        set z0 : Space := state a.par.T 1 (1/2) with hz0def
        have hz0 : z0 ∈ timeClosure a.par.T := by
          simp [z0, timeClosure, state, hT.le]; norm_num
        have hv0 : flatten v z0 ≤ m := by
          have : flatten v z0 = Utilde (crra a) a.par.T 1 := by
            simp only [z0, flatten, state]
            simpa using hPDE.2 1 one_pos (1/2) ⟨by norm_num, by norm_num⟩
          rw [this]; exact hUt 1 le_rfl
        have hcont : ContinuousWithinAt (flatten v) (timeClosure a.par.T) z0 :=
          hC.1.continuousOn z0 hz0
        obtain ⟨ε, hε, hεball⟩ := Metric.continuousWithinAt_iff.mp hcont (-m/2) (by linarith)
        set d : ℝ := min (min (ε/2) (1/4)) a.par.T with hd
        have hd0 : 0 < d := lt_min (lt_min (by linarith) (by norm_num)) hT
        have hdε : d ≤ ε/2 := (min_le_left _ _).trans (min_le_left _ _)
        have hd4 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_right _ _)
        have hdT : d ≤ a.par.T := min_le_right _ _
        set R : Set Space := {z | z 0 ∈ Ioo (a.par.T - d) a.par.T ∧ 1 < z 1 ∧
            z 2 ∈ Ioo (1/2 - d) (1/2 + d)} with hRdef
        have hRdom : R ⊆ domain a.par.T := by
          rintro z ⟨⟨h1, h2⟩, h3, h4, h5⟩
          refine ⟨⟨by linarith, h2⟩, by linarith, by linarith, by linarith⟩
        have hRv : ∀ z ∈ R, flatten v z < m/2 := by
          rintro z hz
          obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hz
          have hmem : state (z 0) 1 (z 2) ∈ timeClosure a.par.T := by
            simp only [timeClosure, state, mem_setOf_eq]
            simp
            refine ⟨⟨by linarith, h2.le⟩, by linarith, by linarith⟩
          have hdist : dist (state (z 0) 1 (z 2)) z0 < ε := by
            rw [EuclideanSpace.dist_eq]
            simp [z0, state, Fin.sum_univ_three, Real.dist_eq]
            rw [Real.sqrt_lt' hε]
            have e1 : (z 0 - a.par.T) ^ 2 < d ^ 2 := by
              exact sq_lt_sq' (by linarith) (by linarith)
            have e2 : (z 2 - 2⁻¹) ^ 2 < d ^ 2 := by
              exact sq_lt_sq' (by linarith) (by linarith)
            nlinarith
          have h6 := hεball hmem hdist
          rw [Real.dist_eq, abs_lt] at h6
          have h7 : v (z 0) 1 (z 2) < m / 2 := by
            have : flatten v (state (z 0) 1 (z 2)) = v (z 0) 1 (z 2) := by simp [flatten, state]
            linarith
          have h8 : v (z 0) (z 1) (z 2) ≤ v (z 0) 1 (z 2) :=
            hanti (z 0) ⟨by linarith, h2⟩ (z 2) ⟨by linarith, by linarith⟩
              (show (0:ℝ) < 1 by norm_num) (show (0:ℝ) < z 1 by linarith) h3.le
          show v (z 0) (z 1) (z 2) < m / 2
          linarith
        -- R is open, measurable, of infinite measure
        have hcoord : ∀ i : Fin 3, Continuous fun z : Space => z i := fun i => by fun_prop
        have hRopen : IsOpen R :=
          (isOpen_Ioo.preimage (hcoord 0)).inter
            ((isOpen_Ioi.preimage (hcoord 1)).inter (isOpen_Ioo.preimage (hcoord 2)))
        have hRmeas : MeasurableSet R := hRopen.measurableSet
        have hRvol : volume R = ⊤ := by
          have hpre : R = (WithLp.ofLp) ⁻¹' (Set.pi univ
              ![Ioo (a.par.T - d) a.par.T, Ioi 1, Ioo (1/2 - d) (1/2 + d)]) := by
            ext z
            simp [R, Fin.forall_fin_succ]
          rw [hpre, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
            (MeasurableSet.univ_pi (fun i => by fin_cases i <;> simp [measurableSet_Ioo, measurableSet_Ioi])).nullMeasurableSet,
            volume_pi_pi, Fin.prod_univ_three]
          simp [Real.volume_Ioo, Real.volume_Ioi, hd0, ENNReal.mul_top, ENNReal.top_mul]
        -- the zeroth-order weak derivative
        obtain ⟨_, hα⟩ := hW
        obtain ⟨g, ⟨hfloc, hgloc, hint⟩, hgL⟩ := hα ![0,0,0] (by unfold orders; exact Finset.mem_insert_self _ _)
        have hmd : ∀ φ : Space → ℝ, HunterPDE.Shared.multiDeriv φ ![0,0,0] = φ := fun φ => by
          simp [HunterPDE.Shared.multiDeriv, HunterPDE.Shared.multiIndexList,
            HunterPDE.Shared.iteratedPartial, List.finRange]
        have hae : ∀ᵐ x ∂(volume : Measure Space), x ∈ R → g x - flatten v x = 0 := by
          apply hRopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
          · exact (hgloc.sub hfloc).mono_set hRdom
          · intro φ hφ1 hφ2 hφ3
            have hKdom : tsupport φ ⊆ domain a.par.T := hφ3.trans hRdom
            have h0 := hint φ ⟨hφ1, hφ2, hKdom⟩
            rw [hmd] at h0
            simp only [Matrix.cons_val_zero, Fin.sum_univ_three, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, add_zero, pow_zero,
              one_mul] at h0
            have hzero : ∀ (F : Space → ℝ), ∀ x, x ∉ domain a.par.T → F x * φ x = 0 := by
              intro F x hx
              rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hKdom h)), mul_zero]
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero g),
              setIntegral_eq_integral_of_forall_compl_eq_zero (hzero (flatten v))] at h0
            have hsupp : ∀ (F : Space → ℝ), Function.support (fun x => F x * φ x) ⊆ tsupport φ :=
              fun F => (Function.support_mul_subset_right _ _).trans (subset_tsupport _)
            have hIg : Integrable (fun x => g x * φ x) := by
              rw [← integrableOn_iff_integrable_of_support_subset (hsupp g)]
              exact (hgloc.integrableOn_compact_subset hKdom hφ2).mul_continuousOn
                hφ1.continuous.continuousOn hφ2
            have hIf : Integrable (fun x => flatten v x * φ x) := by
              rw [← integrableOn_iff_integrable_of_support_subset (hsupp (flatten v))]
              exact (hfloc.integrableOn_compact_subset hKdom hφ2).mul_continuousOn
                hφ1.continuous.continuousOn hφ2
            have : (fun x => φ x • (g x - flatten v x)) =
                fun x => g x * φ x - flatten v x * φ x := by
              funext x; rw [smul_eq_mul]; ring
            rw [this, integral_sub hIg hIf, h0, sub_self]
        set μR : Measure Space := volume.restrict R
        have hgR : MemLp g (ENNReal.ofReal q) μR := hgL.mono_measure (Measure.restrict_mono hRdom le_rfl)
        have heq : g =ᵐ[μR] flatten v :=
          (ae_restrict_iff' hRmeas).mpr (hae.mono fun x hx hxR => sub_eq_zero.mp (hx hxR))
        have hfR : MemLp (flatten v) (ENNReal.ofReal q) μR := hgR.ae_eq heq
        have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
        have hc0 : Real.toNNReal (-m/2) ≠ 0 := by
          rw [Ne, Real.toNNReal_eq_zero, not_le]; linarith
        have hfin := hfR.meas_ge_lt_top hq0 ENNReal.ofReal_ne_top hc0
        have hsub : R ⊆ {x | Real.toNNReal (-m/2) ≤ ‖flatten v x‖₊} := by
          intro x hx
          have := hRv x hx
          show Real.toNNReal (-m/2) ≤ ‖flatten v x‖₊
          rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm, Real.norm_eq_abs]
          rw [abs_of_neg (by linarith)]; linarith
        have hge : μR R ≤ μR {x | Real.toNNReal (-m/2) ≤ ‖flatten v x‖₊} := measure_mono hsub
        rw [Measure.restrict_apply_self, hRvol] at hge
        exact absurd (lt_of_le_of_lt hge hfin) (lt_irrefl _)
