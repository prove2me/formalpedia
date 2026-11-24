-- Prove2me | solution 1 for ObjectCentric.inferred_slot_depends_on_some_slot
-- status  : ACCEPTED   (prove)
-- author  : @fangshuming
-- created : 2026-11-24T10:32:45.887058+00:00
-- url     : https://prove2.me/submissions/20c98576-ce98-4753-b146-67fd03e32a40

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory
open ObjectCentric
open Filter
open scoped Topology

set_option autoImplicit false

/-- Top-level solution theorem matching the official binders and conclusion. -/
 theorem solution {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X) :
    ∀ (z : Lat K M) (i : Fin K), ∃ j : Fin K, slotBlock (fun w => ghat (f w)) z j i ≠ 0 := by
  classical
  intro z i
  -- Define h = ghat ∘ f
  let h : Lat K M → Lat K M := fun w => ghat (f w)
  -- Suppose all blocks in column i vanish; we derive a contradiction
  by_contra hneg
  push_neg at hneg
  -- hneg : ∀ j, slotBlock h z j i = 0
  have hzeroBlocks : ∀ j : Fin K, slotBlock h z j i = 0 := hneg
  -- Choose a coordinate in the slot i
  let b : Fin M := ⟨0, hM⟩
  -- Direction concentrated on slot i and coordinate b
  let v : Lat K M := Pi.single i (Pi.single b 1)
  have hv_ne : v ≠ 0 := by
    intro hv
    have : v i b = 1 := by simp [v]
    have : (0 : ℝ) = 1 := by simpa [hv]
    exact zero_ne_one this
  -- From zeroBlocks, the derivative along v vanishes in every output coordinate
  have h_dv_zero : fderiv ℝ h z v = 0 := by
    funext j a
    -- entry equals the slotBlock entry (a,b) which is zero
    have : slotBlock h z j i a b = 0 := by
      simpa using congrArg (fun M => M a b) (hzeroBlocks j)
    simpa [slotBlock, v] using this
  -- Consider L = g ∘ fhat; we have (L ∘ h) = id
  have hLh_id : (fun w => g (fhat (h w))) = (fun w => w) := by
    funext w
    have hwX : fhat (h w) ∈ X := by
      -- since Set.range fhat = X
      have : fhat (h w) ∈ Set.range fhat := ⟨h w, rfl⟩
      simpa [hhat.2.2] using this
    -- use hhat.2.3: ghat (fhat x) = x and hf.2.3: g (f x) = x
    have : fhat (h w) = f w := by
      -- Since f w ∈ X = Set.range fhat, write f w = fhat y and use ghat ∘ fhat = id
      have hwXfhat : f w ∈ Set.range fhat := by
        have : f w ∈ Set.range f := ⟨w, rfl⟩
        have hwXf : f w ∈ X := by simpa [hf.2.2] using this
        simpa [hhat.2.2] using hwXf
      rcases hwXfhat with ⟨y, hy⟩
      calc
        fhat (h w) = fhat (ghat (f w)) := rfl
        _ = fhat (ghat (fhat y)) := by simpa [hy]
        _ = fhat y := by simpa [hhat.2.2.2 y]
        _ = f w := by simpa [hy]
    simpa [this, hf.2.2.2]
  -- Differentiate the identity at z along v
  have h_deriv_id : fderiv ℝ (fun w : Lat K M => g (fhat (h w))) z v = v := by
    -- since it's the identity function
    simpa [hLh_id]
  -- Compute the derivative of the composition at z along v using chain rule
  -- First, gather differentiability assumptions
  have h_memX : f z ∈ X := by
    have : f z ∈ Set.range f := ⟨z, rfl⟩
    simpa [hf.2.2] using this
  -- Differentiability of inner and outer maps for the chain rule
  have h_cont_f : ContDiff ℝ 1 f := hf.1
  have h_cont_fhat : ContDiff ℝ 1 fhat := hhat.1
  have h_contWithin_ghat : ContDiffWithinAt ℝ 1 ghat X (f z) :=
    (hhat.2.1.contDiffWithinAt (h_memX))
  have h_contAt_f : ContDiffAt ℝ 1 f z := h_cont_f.contDiffAt
  have h_diffAt_f : DifferentiableAt ℝ f z := h_contAt_f.differentiableAt (by decide)
  have h_hasAt_f : HasFDerivAt f (fderiv ℝ f z) z := h_diffAt_f.hasFDerivAt
  have h_contAt_fhat : ContDiffAt ℝ 1 fhat (h z) := h_cont_fhat.contDiffAt
  have h_diffAt_fhat : DifferentiableAt ℝ fhat (h z) := h_contAt_fhat.differentiableAt (by decide)
  have h_hasAt_fhat : HasFDerivAt fhat (fderiv ℝ fhat (h z)) (h z) := h_diffAt_fhat.hasFDerivAt
  have h_diffWithin_ghat : DifferentiableWithinAt ℝ ghat X (f z) :=
    h_contWithin_ghat.differentiableWithinAt (by decide)
  have h_hasWithin_ghat : HasFDerivWithinAt ghat (fderivWithin ℝ ghat X (f z)) X (f z) :=
    h_diffWithin_ghat.hasFDerivWithinAt
  have h_contWithin_g : ContDiffWithinAt ℝ 1 g X (fhat (h z)) := (hf.2.1.contDiffWithinAt (by
    -- fhat (h z) ∈ X by range identity
    have : fhat (h z) ∈ Set.range fhat := ⟨h z, rfl⟩
    simpa [hhat.2.2] using this))
  have h_diffWithin_g : DifferentiableWithinAt ℝ g X (fhat (h z)) :=
    h_contWithin_g.differentiableWithinAt (by decide)
  have h_hasWithin_g : HasFDerivWithinAt g (fderivWithin ℝ g X (fhat (h z))) X (fhat (h z)) :=
    h_diffWithin_g.hasFDerivWithinAt
  -- Chain rule to compute derivative of the triple composition at z
  have h_event_X : ∀ᶠ x' in 𝓝 z, f x' ∈ X :=
    Eventually.of_forall (fun x' => by
      have : f x' ∈ Set.range f := ⟨x', rfl⟩
      simpa [hf.2.2] using this)
  have h_hasAt_h : HasFDerivAt h (((fderivWithin ℝ ghat X (f z)) ∘L (fderiv ℝ f z))) z :=
    HasFDerivWithinAt.comp_hasFDerivAt (f:=f) (x:=z) (g:=ghat)
      (g':=fderivWithin ℝ ghat X (f z)) (t:=X) h_hasWithin_ghat h_hasAt_f h_event_X
  have h_event_X2 : ∀ᶠ y in 𝓝 (h z), fhat y ∈ X :=
    Eventually.of_forall (fun y => by
      have : fhat y ∈ Set.range fhat := ⟨y, rfl⟩
      simpa [hhat.2.2] using this)
  have h_hasAt_L : HasFDerivAt (fun w => g (fhat w))
      (((fderivWithin ℝ g X (fhat (h z))) ∘L (fderiv ℝ fhat (h z)))) (h z) :=
    HasFDerivWithinAt.comp_hasFDerivAt (f:=fhat) (x:=(h z)) (g:=g)
      (g':=fderivWithin ℝ g X (fhat (h z))) (t:=X) h_hasWithin_g h_hasAt_fhat h_event_X2
  have h_comp := h_hasAt_L.comp z h_hasAt_h
  -- Apply the computed derivative to v: since fderiv h z v = 0, the chain gives 0
  have hv0' :
      fderiv ℝ (fun w => g (fhat (h w))) z v = 0 := by
    -- expand derivative map and evaluate on v
    have h_fderiv_comp := (h_hasAt_L.comp z h_hasAt_h).fderiv
    have h_fderiv_h := h_hasAt_h.fderiv
    -- Evaluate the composed linear map on v and use h_dv_zero
    have : (((fderivWithin ℝ g X (fhat (h z))).comp (fderiv ℝ fhat (h z))).comp
            ((fderivWithin ℝ ghat X (f z)).comp (fderiv ℝ f z))) v = 0 := by
      -- inner equals (fderiv h z) by h_fderiv_h
      have : ((fderivWithin ℝ ghat X (f z)).comp (fderiv ℝ f z)) v = (fderiv ℝ h z) v := by
        simpa [h_fderiv_h] using rfl
      -- therefore the whole composition applied to v is outer ∘ (fderiv h z v) = outer 0 = 0
      simpa [this, h_dv_zero]
    -- turn linear map equality into derivative equality
    simpa [Function.comp] using congrArg (fun L => L v) h_fderiv_comp ▸ this
  -- But by identity, its derivative equals v, contradiction
  have : v = 0 := by
    simpa [h_deriv_id] using hv0'
  exact hv_ne this
