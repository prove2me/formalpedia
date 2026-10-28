-- Prove2me | solution 1 for ProxADMMLC.Conv.eq_3_5
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:33.434352+00:00
-- url     : https://prove2.me/submissions/3a6598b4-7678-4d7b-80b5-caa4d8766bb6

import Definitions.Def_ProxADMMLC_Conv_Setting
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
open ProxADMMLC.Conv

theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (hdiff : Differentiable ℝ f) (Γ p c α β : ℝ)
    (hp : 0 < p) (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst)
    (x z : ℕ → E n) (y : ℕ → E m) (hrun : IsRun f A b ℓ u Γ p c α β x y z) :
    (∀ w ∈ box ℓ u, sInf (f '' feas A b ℓ u) ≤ Mval f p xst w) ∧
      ∀ t, Mval f p xst (z t) ≤ phi f A b Γ p xs xst (x t) (z t) (y t) ∧
        sInf (f '' feas A b ℓ u) ≤ Mval f p xst (z t) := by
  have hbox : IsCompact (box ℓ u) := by
    have heq : box ℓ u = WithLp.toLp 2 '' (Set.Icc ℓ u) := by
      ext w
      constructor
      · intro hw
        exact ⟨WithLp.ofLp w,⟨fun i => (hw i).1,fun i => (hw i).2⟩,rfl⟩
      · rintro ⟨q,hq,rfl⟩
        exact fun i => ⟨hq.1 i,hq.2 i⟩
    rw [heq]
    exact isCompact_Icc.image (PiLp.continuous_toLp (p:=2) (β:=fun _ : Fin n => ℝ))
  have hb : BddBelow (f '' feas A b ℓ u) :=
    (hbox.bddBelow_image hdiff.continuous.continuousOn).mono
      (by rintro _ ⟨w,hw,rfl⟩; exact ⟨w,hw.1,rfl⟩)
  have hM (w : E n) : sInf (f '' feas A b ℓ u) ≤ Mval f p xst w := by
    have h0 := csInf_le hb (show f (xst w) ∈ f '' feas A b ℓ u from ⟨xst w,(hxst w).1,rfl⟩)
    have hpos : 0 ≤ p/2*‖xst w-w‖^2 := mul_nonneg (by positivity) (sq_nonneg _)
    dsimp only [Mval]
    linarith
  have hproj (v : E n) : boxProj ℓ u v ∈ box ℓ u := by
    intro i
    change ℓ i ≤ (if v i < ℓ i then ℓ i else if v i ≤ u i then v i else u i) ∧
      (if v i < ℓ i then ℓ i else if v i ≤ u i then v i else u i) ≤ u i
    split_ifs with h1 h2
    · exact ⟨le_rfl,(hℓu i).le⟩
    · exact ⟨le_of_not_gt h1,h2⟩
    · exact ⟨(hℓu i).le,le_rfl⟩
  have hx : ∀ t,x t ∈ box ℓ u := by
    intro t
    cases t with
    | zero => exact hrun.1
    | succ t => rw [(hrun.2.2 t).2.1]; exact hproj _
  have hdual (yy : E m) (zz : E n) : dval f A b Γ p xs yy zz ≤ Mval f p xst zz := by
    have he : A (xst zz)=b := (hxst zz).1.2
    have hm := (hxs yy zz).2 (xst zz) (hxst zz).1.1
    simpa [dval,K,Mval,he] using hm
  refine ⟨fun w hw => hM w,?_⟩
  intro t
  refine ⟨?_,hM (z t)⟩
  have h1 : dval f A b Γ p xs (y t) (z t) ≤ K f A b Γ p (x t) (z t) (y t) :=
    (hxs (y t) (z t)).2 (x t) (hx t)
  have h2 := hdual (y t) (z t)
  unfold phi
  linarith

#print axioms solution

