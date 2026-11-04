-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.eq_4_33
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:25:35.065733+00:00
-- url     : https://prove2.me/submissions/ea010db8-0f9d-4f8c-b0a6-9c83477d44b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Theorems.Thm_RiskAverseSDDP_Convergence_proposition_3_1
open Filter Topology
open RiskAverseSDDP.Convergence

namespace RASDDPEq433

lemma snoc_continuous {n s : ℕ} (x : Hist n s) : Continuous (fun y => x.snoc y) := by
  unfold Hist.snoc
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; exact continuous_id
  · simp only [Fin.snoc_castSucc]; exact continuous_const

lemma snoc_mem_prodSet {T n M q p : ℕ} (D : Model T n M q p) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ D.Xc 1) : (Hist.empty n).snoc y ∈ D.prodSet 1 := by
  intro i
  have hi : i = Fin.last 0 := Subsingleton.elim _ _
  subst hi
  show (WithLp.toLp 2 _ : Hist n 1) (Fin.last 0) ∈ D.Xc ((Fin.last 0).val + 1)
  rw [PiLp.toLp_apply, Fin.snoc_last]
  simpa using hy

lemma feas0_closed {T n M q p : ℕ} [NeZero M] (D : Model T n M q p)
    (hX : IsClosed (D.Xc 1)) (hg : ∀ i, LowerSemicontinuous (fun z => D.g 1 0 D.x0 z i)) :
    IsClosed (D.feas 0 0 (Hist.empty n)) := by
  simp only [Model.feas, Set.setOf_and]
  refine hX.inter (IsClosed.inter ?_ ?_)
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      ((hg i).comp (snoc_continuous (Hist.empty n))).isClosed_preimage 0
  · refine isClosed_eq ?_ continuous_const
    refine continuous_finset_sum _ fun τ _ => ?_
    refine (D.A (0 + 1) 0 τ).continuous_of_finiteDimensional.comp ?_
    refine Fin.cases ?_ (fun i => ?_) τ
    · simp only [Fin.cons_zero]; exact continuous_const
    · simp only [Fin.cons_succ]
      exact (PiLp.continuous_apply 2 _ i).comp (snoc_continuous _)

lemma aux_real (F0 Qv Mv : EReal) (h1 : F0 ≠ ⊥) (h2 : F0 ≠ ⊤) (h3 : Qv ≠ ⊥) (h4 : Qv ≠ ⊤)
    (hg1 : Qv - Mv ≠ ⊥) (hg2 : Qv - Mv ≠ ⊤) :
    F0 = (((F0 + Mv).toReal + (Qv - Mv).toReal - Qv.toReal : ℝ) : EReal) := by
  lift F0 to ℝ using ⟨h2, h1⟩ with fv
  lift Qv to ℝ using ⟨h4, h3⟩ with qv
  induction Mv using EReal.rec with
  | bot => exact absurd (EReal.sub_bot (EReal.coe_ne_bot qv)) hg2
  | top => exact absurd (by simp) hg1
  | coe m =>
    rw [← EReal.coe_add, ← EReal.coe_sub, EReal.toReal_coe, EReal.toReal_coe, EReal.toReal_coe]
    congr 1; ring

end RASDDPEq433

open RASDDPEq433 in
theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ) (hT : 1 ≤ T)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r)
    (hval : Tendsto (fun k => D.stageVal 0 0 (r.Qm k 1) (Hist.empty n)) atTop (𝓝 D.Q1))
    (h432 : Tendsto
      (fun k => D.Q 1 (r.hist (k + 1) 0 Fin.elim0) - r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0))
      atTop (𝓝 0)) :
    ∀ xs : EuclideanSpace ℝ (Fin n),
      MapClusterPt xs atTop (fun k => r.x k 0 Fin.elim0) → D.IsFirstStageOptimal xs := by
  intro xs hxs
  have hε : 0 < ε := hH2.1
  obtain ⟨hX, hf, hgc, hdom, -, -⟩ := hH2.2 0 hT
  have h0 : (0 : Fin M) ∈ Model.Rlz (M := M) (0 + 1) := by simp [Model.Rlz]
  obtain ⟨hprop, -, hlsc⟩ := hf 0 h0
  obtain ⟨-, hfin, hcont⟩ := proposition_3_1 D ε hS hH2 1 le_rfl hT (ε / 2) (by linarith)
    (by linarith)
  set e := Hist.empty n
  have he : e ∈ Metric.cthickening ε (D.prodSet 0) :=
    Metric.self_subset_cthickening _ (fun i => Fin.elim0 i)
  have hPC : ∀ y ∈ D.Xc 1, e.snoc y ∈ Metric.cthickening (ε / 2) (D.prodSet 1) := fun y hy =>
    Metric.self_subset_cthickening _ (snoc_mem_prodSet D y hy)
  -- the forward pass at the first-stage node
  have hfw : ∀ k, r.x (k + 1) 0 Fin.elim0 ∈ D.feas 0 0 e ∧
      D.stageVal 0 0 (r.Qm k 1) e =
        D.f 1 0 (e.snoc (r.x (k + 1) 0 Fin.elim0)) + r.Qm k 1 (e.snoc (r.x (k + 1) 0 Fin.elim0)) := by
    intro k
    obtain ⟨_, hxfeas, hxmin⟩ := hr.2.2.1 k 0 Fin.elim0 hT
    have hphist : r.phist (k + 1) 0 Fin.elim0 = e := rfl
    have hnr : nodeRlz 0 (Fin.elim0 : Fin 0 → Fin M) = 0 := rfl
    rw [hphist, hnr] at hxfeas hxmin
    refine ⟨hxfeas, le_antisymm ?_ (le_iInf₂ fun y hy => hxmin y hy)⟩
    exact iInf₂_le (f := fun y _ => D.f (0 + 1) 0 (e.snoc y) + r.Qm k (0 + 1) (e.snoc y))
      _ hxfeas
  -- a subsequence converging to xs
  obtain ⟨φ, hφ, hφc⟩ := hxs.tendsto_subseq
  set ψ : ℕ → ℕ := fun l => φ (l + 1) - 1
  have hψ1 : ∀ l, ψ l + 1 = φ (l + 1) := fun l => by
    have := hφ.id_le (l + 1)
    show φ (l + 1) - 1 + 1 = φ (l + 1)
    simp only [id] at this; omega
  have hψt : Tendsto ψ atTop atTop := tendsto_atTop_mono (fun l => by
    have := hφ.id_le (l + 1)
    show l ≤ φ (l + 1) - 1
    simp only [id] at this; omega) tendsto_id
  set w : ℕ → EuclideanSpace ℝ (Fin n) := fun l => r.x (ψ l + 1) 0 Fin.elim0
  have hw : Tendsto w atTop (𝓝 xs) := by
    have := hφc.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun l => ?_
    simp only [Function.comp, w, hψ1]
  have hwX : ∀ l, w l ∈ D.feas 0 0 e := fun l => (hfw (ψ l)).1
  -- feasibility of xs
  have hgl : ∀ i, LowerSemicontinuous (fun z => D.g 1 0 D.x0 z i) := fun i => (hgc 0 h0 i).2
  have hxsF : xs ∈ D.feas 0 0 e :=
    (feas0_closed D hX.2.2.isClosed hgl).mem_of_tendsto hw (Eventually.of_forall hwX)
  have hxsX : xs ∈ D.Xc 1 := hxsF.1
  refine ⟨hxsF, le_antisymm ?_ ?_⟩
  swap
  · exact iInf₂_le (f := fun y _ => D.f (0 + 1) 0 (e.snoc y) + D.Q (0 + 1) (e.snoc y)) xs hxsF
  -- finiteness of Q1
  have hQ1t : D.Q1 ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (iInf₂_le (f := fun y _ =>
      D.f (0 + 1) 0 (e.snoc y) + D.Q (0 + 1) (e.snoc y)) xs hxsF)
    have h1 : D.f 1 0 (e.snoc xs) ≠ ⊤ := (hdom 0 h0 e he xs hxsX).ne
    have h2 := (hfin _ (hPC xs hxsX)).2
    exact EReal.add_ne_top h1 h2
  have hQ1b : D.Q1 ≠ ⊥ := by
    have hlsc' : LowerSemicontinuousOn (fun y => D.f 1 0 (e.snoc y)) (D.Xc 1) :=
      (hlsc.comp (snoc_continuous e)).lowerSemicontinuousOn _
    obtain ⟨y0, _, hy0⟩ := hlsc'.exists_isMinOn hX.1 hX.2.2
    have hcont' : ContinuousOn (fun y => (D.Q 1 (e.snoc y)).toReal) (D.Xc 1) :=
      hcont.comp (snoc_continuous e).continuousOn (fun y hy => hPC y hy)
    obtain ⟨y1, _, hy1⟩ := hX.2.2.exists_isMinOn hX.1 hcont'
    have hf0 : D.f 1 0 (e.snoc y0) ≠ ⊥ := hprop.1 _
    have hlow : ((D.f 1 0 (e.snoc y0)).toReal + (D.Q 1 (e.snoc y1)).toReal : EReal) ≤ D.Q1 := by
      refine le_iInf₂ fun y hy => ?_
      have hyX : y ∈ D.Xc 1 := hy.1
      have h1 : D.f 1 0 (e.snoc y0) ≤ D.f 1 0 (e.snoc y) := hy0 hyX
      have h2 : (D.Q 1 (e.snoc y1)).toReal ≤ (D.Q 1 (e.snoc y)).toReal := hy1 hyX
      have hfy2 : D.f 1 0 (e.snoc y) ≠ ⊤ := (hdom 0 h0 e he y hyX).ne
      have hf0t : D.f 1 0 (e.snoc y0) ≠ ⊤ := ne_top_of_le_ne_top hfy2 h1
      have hQy := hfin _ (hPC y hyX)
      have e1 : ((D.f 1 0 (e.snoc y0)).toReal : EReal) = D.f 1 0 (e.snoc y0) :=
        EReal.coe_toReal hf0t hf0
      have e2 : ((D.Q 1 (e.snoc y)).toReal : EReal) = D.Q 1 (e.snoc y) :=
        EReal.coe_toReal hQy.2 hQy.1
      show _ ≤ D.f (0 + 1) 0 (e.snoc y) + D.Q (0 + 1) (e.snoc y)
      refine add_le_add (by rw [e1]; exact h1) ?_
      rw [← e2]; exact_mod_cast h2
    exact ne_bot_of_le_ne_bot (by rw [← EReal.coe_add]; exact EReal.coe_ne_bot _) hlow
  lift D.Q1 to ℝ using ⟨hQ1t, hQ1b⟩ with c hc
  -- real sequences along the subsequence
  have hQxs := hfin _ (hPC xs hxsX)
  set qx := (D.Q 1 (e.snoc xs)).toReal
  have hQw : Tendsto (fun l => (D.Q 1 (e.snoc (w l))).toReal) atTop (𝓝 qx) := by
    have hcw := hcont (e.snoc xs) (hPC xs hxsX)
    refine hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun l => ?_⟩)
    · exact ((snoc_continuous e).tendsto xs).comp hw
    · exact hPC _ (hwX l).1
  have hV := hval.comp hψt
  have hG := h432.comp hψt
  -- eventually everything is finite
  have hVf : ∀ᶠ l in atTop, D.stageVal 0 0 (r.Qm (ψ l) 1) e ≠ ⊥ ∧
      D.stageVal 0 0 (r.Qm (ψ l) 1) e ≠ ⊤ := by
    have h1 := hV.eventually (lt_mem_nhds (EReal.coe_lt_coe_iff.2 (sub_one_lt c)))
    have h2 := hV.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.2 (lt_add_one c)))
    filter_upwards [h1, h2] with l hl1 hl2
    exact ⟨ne_bot_of_gt hl1, ne_top_of_lt hl2⟩
  have hGf : ∀ᶠ l in atTop, (fun k => D.Q 1 (r.hist (k + 1) 0 Fin.elim0) -
      r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0)) (ψ l) ≠ ⊥ ∧
      (fun k => D.Q 1 (r.hist (k + 1) 0 Fin.elim0) -
      r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0)) (ψ l) ≠ ⊤ := by
    have h1 := hG.eventually (lt_mem_nhds (show (-1 : EReal) < 0 by norm_num))
    have h2 := hG.eventually (gt_mem_nhds (show (0 : EReal) < 1 by norm_num))
    filter_upwards [h1, h2] with l hl1 hl2
    exact ⟨ne_bot_of_gt hl1, ne_top_of_lt hl2⟩
  -- the real parts of f along the subsequence converge to c - qx
  have hfw' : ∀ᶠ l in atTop, D.f 1 0 (e.snoc (w l)) =
      ((D.stageVal 0 0 (r.Qm (ψ l) 1) e).toReal +
        ((fun k => D.Q 1 (r.hist (k + 1) 0 Fin.elim0) - r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0))
          (ψ l)).toReal - (D.Q 1 (e.snoc (w l))).toReal : ℝ) := by
    filter_upwards [hGf] with l ⟨hg1, hg2⟩
    have hrel : D.stageVal 0 0 (r.Qm (ψ l) 1) e =
        D.f 1 0 (e.snoc (w l)) + r.Qm (ψ l) 1 (e.snoc (w l)) := (hfw (ψ l)).2
    have hq := hfin _ (hPC _ (hwX l).1)
    have key := aux_real (D.f 1 0 (e.snoc (w l))) (D.Q 1 (e.snoc (w l)))
      (r.Qm (ψ l) 1 (e.snoc (w l))) (hprop.1 _) (hdom 0 h0 e he _ (hwX l).1).ne hq.1 hq.2 hg1 hg2
    rw [hrel]
    exact key
  have hlimf : Tendsto (fun l =>
      (D.stageVal 0 0 (r.Qm (ψ l) 1) e).toReal +
        ((fun k => D.Q 1 (r.hist (k + 1) 0 Fin.elim0) - r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0))
          (ψ l)).toReal - (D.Q 1 (e.snoc (w l))).toReal) atTop (𝓝 (c + 0 - qx)) := by
    have h1 := (EReal.tendsto_toReal (a := (c : EReal)) (EReal.coe_ne_top c)
      (EReal.coe_ne_bot c)).comp hV
    have h2 := (EReal.tendsto_toReal (a := 0) (by simp) (by simp)).comp hG
    simp only [EReal.toReal_coe, EReal.toReal_zero] at h1 h2
    exact (h1.add h2).sub hQw
  simp only [add_zero] at hlimf
  -- lower semicontinuity of f at xs
  have hF : LowerSemicontinuous (fun y => D.f 1 0 (e.snoc y)) := hlsc.comp (snoc_continuous e)
  have hfle : D.f 1 0 (e.snoc xs) ≤ ((c - qx : ℝ) : EReal) := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hev1 := hw.eventually (hF xs y hy2)
    have hev2 := hlimf.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.1 hy1))
    obtain ⟨l, hl1, hl2, hl3⟩ := (hev1.and (hev2.and hfw')).exists
    simp only [Function.comp] at hl1
    rw [hl3] at hl1
    exact absurd (EReal.coe_lt_coe_iff.1 hl1) (not_lt.2 hl2.le)
  have hQ : D.Q (0 + 1) (e.snoc xs) = (qx : EReal) := (EReal.coe_toReal hQxs.2 hQxs.1).symm
  show D.f (0 + 1) 0 (e.snoc xs) + D.Q (0 + 1) (e.snoc xs) ≤ (c : EReal)
  rw [hQ]
  calc D.f (0 + 1) 0 (e.snoc xs) + (qx : EReal) ≤ ((c - qx : ℝ) : EReal) + (qx : EReal) :=
        add_le_add_left hfle _
    _ = (c : EReal) := by rw [← EReal.coe_add]; congr 1; ring
