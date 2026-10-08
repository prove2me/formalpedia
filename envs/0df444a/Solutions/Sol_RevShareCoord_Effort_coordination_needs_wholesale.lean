-- Prove2me | solution 1 for RevShareCoord.Effort.coordination_needs_wholesale
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:37:33.703102+00:00
-- url     : https://prove2.me/submissions/6ebbc0ec-4415-418c-b1c2-aed37e50c037

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Model

open RevShareCoord.Effort in
/-- Interior maximiser in the second coordinate: the derivative vanishes. -/
theorem rsc4639_deriv_e_zero (f : ℝ → ℝ → ℝ) (q e d : ℝ) (he : 0 < e)
    (hmax : IsMaxOn (fun x : ℝ × ℝ => f x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0) (q, e))
    (hq : 0 ≤ q)
    (hd : HasDerivWithinAt (fun e' => f q e') d (Set.Ici 0) e) : d = 0 := by
  have hn : Set.Ici (0:ℝ) ∈ nhds e := Ici_mem_nhds he
  have h1 : IsMaxOn (fun e' => f q e') (Set.Ici 0) e := by
    intro y hy
    have := hmax (show ((q, y) : ℝ × ℝ) ∈ Set.Ici 0 ×ˢ Set.Ici 0 from ⟨hq, hy⟩)
    simpa using this
  exact (h1.isLocalMax hn).hasDerivAt_eq_zero (hd.hasDerivAt hn)

/-- Interior maximiser in the first coordinate: the derivative vanishes. -/
theorem rsc4639_deriv_q_zero (f : ℝ → ℝ → ℝ) (q e d : ℝ) (hq : 0 < q)
    (hmax : IsMaxOn (fun x : ℝ × ℝ => f x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0) (q, e))
    (he : 0 ≤ e)
    (hd : HasDerivWithinAt (fun q' => f q' e) d (Set.Ici 0) q) : d = 0 := by
  have hn : Set.Ici (0:ℝ) ∈ nhds q := Ici_mem_nhds hq
  have h1 : IsMaxOn (fun q' => f q' e) (Set.Ici 0) q := by
    intro y hy
    have := hmax (show ((y, e) : ℝ × ℝ) ∈ Set.Ici 0 ×ˢ Set.Ici 0 from ⟨hy, he⟩)
    simpa using this
  exact (h1.isLocalMax hn).hasDerivAt_eq_zero (hd.hasDerivAt hn)

open RevShareCoord.Effort in
theorem solution (M : Model) (qI eI : ℝ) (hqI : 0 < qI) (heI : 0 < eI)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0) (qI, eI))
    (hRe : 0 < M.Re qI eI)
    (φ w : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hret : IsMaxOn (fun x : ℝ × ℝ => M.retailerProfit φ w x.1 x.2)
      (Set.Ici 0 ×ˢ Set.Ici 0) (qI, eI)) :
    φ = 1 ∧ w = M.c ∧ M.supplierProfit φ w qI eI = 0 := by
  have hq0 : (0:ℝ) ≤ qI := hqI.le
  have he0 : (0:ℝ) ≤ eI := heI.le
  have hRe' := M.hasDeriv_e qI eI hq0 he0
  have hRq' := M.hasDeriv_q qI eI hq0 he0
  have hg' := M.hasDeriv_g eI he0
  -- e-derivatives
  have dPe : HasDerivWithinAt (fun e' => M.Pi qI e') (M.Re qI eI - M.g' eI) (Set.Ici 0) eI := by
    have h := (hRe'.sub hg').sub_const (qI * M.c)
    exact h.congr (fun y _ => by simp [Model.Pi]) (by simp [Model.Pi])
  have dRe : HasDerivWithinAt (fun e' => M.retailerProfit φ w qI e')
      (φ * M.Re qI eI - M.g' eI) (Set.Ici 0) eI := by
    have h := ((hRe'.const_mul φ).sub hg').sub_const (qI * w)
    exact h.congr (fun y _ => by simp [Model.retailerProfit]) (by simp [Model.retailerProfit])
  have e1 := rsc4639_deriv_e_zero (fun q e => M.Pi q e) qI eI _ heI hopt hq0 dPe
  have e2 := rsc4639_deriv_e_zero (fun q e => M.retailerProfit φ w q e) qI eI _ heI hret hq0 dRe
  have hφ : φ = 1 := by
    have h : (1 - φ) * M.Re qI eI = 0 := by linarith
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · linarith
  -- q-derivatives
  have dPq : HasDerivWithinAt (fun q' => M.Pi q' eI) (M.Rq qI eI - 1 * M.c) (Set.Ici 0) qI := by
    have h := (hRq'.sub_const (M.g eI)).sub
      ((hasDerivWithinAt_id qI (Set.Ici (0:ℝ))).mul_const M.c)
    exact h.congr (fun y _ => by simp [Model.Pi]) (by simp [Model.Pi])
  have dRq : HasDerivWithinAt (fun q' => M.retailerProfit φ w q' eI)
      (φ * M.Rq qI eI - 1 * w) (Set.Ici 0) qI := by
    have h := ((hRq'.const_mul φ).sub_const (M.g eI)).sub
      ((hasDerivWithinAt_id qI (Set.Ici (0:ℝ))).mul_const w)
    exact h.congr (fun y _ => by simp [Model.retailerProfit]) (by simp [Model.retailerProfit])
  have q1 := rsc4639_deriv_q_zero (fun q e => M.Pi q e) qI eI _ hqI hopt he0 dPq
  have q2 := rsc4639_deriv_q_zero (fun q e => M.retailerProfit φ w q e) qI eI _ hqI hret he0 dRq
  subst hφ
  have hw : w = M.c := by linarith
  refine ⟨rfl, hw, ?_⟩
  simp [Model.supplierProfit, hw]
