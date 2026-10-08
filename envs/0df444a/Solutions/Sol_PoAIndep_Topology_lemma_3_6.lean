-- Prove2me | solution 1 for PoAIndep.Topology.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:43:18.074485+00:00
-- url     : https://prove2.me/submissions/d9dbf57f-1e85-4ae0-a156-311e114887eb

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model
open PoAIndep.Topology

private theorem marginal_cont (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) :
    ContinuousOn (marginalCost ℓ) (Set.Ici 0) := by
  have hd : DifferentiableOn ℝ (fun x => x * ℓ x) (Set.Ici 0) :=
    differentiableOn_id.mul hℓ.1.2.1
  have hm : MonotoneOn (marginalCost ℓ) (Set.Ici 0) := hℓ.2.monotoneOn_derivWithin hd
  let S : Set ℝ := marginalCost ℓ '' Set.Ici 0
  have hS : Set.OrdConnected S := Set.ordConnected_Ici.image_derivWithin hd
  letI : Set.OrdConnected S := hS
  let f : Set.Ici (0 : ℝ) → S := fun x => ⟨marginalCost ℓ x, ⟨x, x.property, rfl⟩⟩
  have hf : Monotone f := fun x y hxy => hm x.property y.property hxy
  have hs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact continuousOn_iff_continuous_restrict.mpr
    (continuous_subtype_val.comp (hf.continuous_of_surjective hs))

private theorem lambda_exists (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) (r : ℝ) (hr : 0 < r) :
    (marginalCost ℓ 0 = ℓ 0 ∧ ℓ 0 ≤ ℓ r ∧ ℓ r ≤ marginalCost ℓ r) ∧
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, marginalCost ℓ (lam * r) = ℓ r := by
  have h0 : marginalCost ℓ 0 = ℓ 0 := by
    have hd := (hasDerivWithinAt_id (0 : ℝ) (Set.Ici 0)).mul
      ((hℓ.1.2.1 0 (by simp)).hasDerivWithinAt)
    simpa [marginalCost, Pi.mul_def, id_def] using hd.derivWithin (uniqueDiffWithinAt_Ici 0)
  have hmono : ℓ 0 ≤ ℓ r := hℓ.1.2.2 (by simp) hr.le hr.le
  have hbound : ℓ r ≤ marginalCost ℓ r := by
    have h := hℓ.2.slope_le_derivWithin (by simp : (0 : ℝ) ∈ Set.Ici 0) hr.le hr
      ((differentiableOn_id.mul hℓ.1.2.1) r hr.le)
    simpa [slope_def_field, marginalCost, ne_of_gt hr] using h
  refine ⟨⟨h0, hmono, hbound⟩, ?_⟩
  have hc : ContinuousOn (marginalCost ℓ) (Set.Icc 0 r) :=
    (marginal_cont ℓ hℓ).mono (fun _ hx => hx.1)
  obtain ⟨y, hy, he⟩ := intermediate_value_Icc hr.le hc ⟨by simpa [h0] using hmono, hbound⟩
  refine ⟨y/r, ⟨div_nonneg hy.1 hr.le, (div_le_one hr).2 hy.2⟩, ?_⟩
  simpa [ne_of_gt hr] using he

private theorem denominator_le_one (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ)
    (x : ℝ) (hx : 0 < x) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hp : 0 < ℓ x) :
    ENNReal.ofReal (lam * (ℓ (lam*x)/ℓ x) + (1-lam)) ≤ 1 := by
  have h0 : 0 ≤ lam*x := mul_nonneg hlam.1 hx.le
  have h1 : lam*x ≤ x := by nlinarith [hlam.2]
  have hm : ℓ (lam*x) ≤ ℓ x := hℓ.1.2.2 h0 hx.le h1
  have hd : ℓ (lam*x)/ℓ x ≤ 1 := (div_le_one hp).2 hm
  apply (ENNReal.ofReal_le_one).2
  nlinarith [mul_nonneg hlam.1 (sub_nonneg.mpr hd)]

private theorem denominator_pos (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ)
    (x : ℝ) (hx : 0 < x) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hp : 0 < ℓ x) : 0 < lam * (ℓ (lam*x)/ℓ x) + (1-lam) := by
  rcases eq_or_lt_of_le hlam.2 with he | he
  · subst lam
    simp [ne_of_gt hp]
  · have hn := mul_nonneg hlam.1 (div_nonneg
      (hℓ.1.1 (lam*x) (mul_nonneg hlam.1 hx.le)) hp.le)
    linarith

private theorem alpha_ge_one (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) :
    1 ≤ anarchyValue L := by
  obtain ⟨ℓ, hmem, y, hy, hne⟩ := hL.1
  have hp : 0 < ℓ (y+1) := lt_of_lt_of_le
    (lt_of_le_of_ne ((hL.2 ℓ hmem).1.1 y hy) (Ne.symm hne))
    ((hL.2 ℓ hmem).1.2.2 hy (show 0 ≤ y+1 by linarith) (show y ≤ y+1 by linarith))
  obtain ⟨lam, hlam, he⟩ := (lambda_exists ℓ (hL.2 ℓ hmem) (y+1) (by linarith)).2
  have hb := denominator_le_one ℓ (hL.2 ℓ hmem) (y+1) (by linarith) lam hlam hp
  calc
    1 ≤ (ENNReal.ofReal (lam * (ℓ (lam*(y+1))/ℓ (y+1)) + (1-lam)))⁻¹ :=
      ENNReal.one_le_inv.mpr hb
    _ ≤ anarchyValue L := by
      unfold anarchyValue anarchyValueFn
      refine le_iSup_of_le ℓ (le_iSup_of_le hmem (le_iSup_of_le (y+1)
        (le_iSup_of_le (by linarith : 0 < y+1) (le_iSup_of_le hp
          (le_iSup_of_le lam (le_iSup_of_le hlam (le_iSup_of_le he ?_)))))))
      rw [ENNReal.ofReal_inv_of_pos (denominator_pos ℓ (hL.2 ℓ hmem)
        (y+1) (by linarith) lam hlam hp)]

theorem solution (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (ℓ : ℝ → ℝ) (hℓ : ℓ ∈ L)
    (x : ℝ) (hx : 0 < x) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hsolve : marginalCost ℓ (lam * x) = ℓ x) :
    (anarchyValue L)⁻¹ ≤
      ENNReal.ofReal (lam * (if ℓ x = 0 then 1 else ℓ (lam * x) / ℓ x) + (1 - lam)) := by
  by_cases hz : ℓ x = 0
  · simp only [hz, ite_true, mul_one, add_sub_cancel]
    simpa using ENNReal.inv_le_inv' (alpha_ge_one L hL)
  · simp only [hz, ite_false]
    rw [← inv_inv (ENNReal.ofReal _)]
    apply ENNReal.inv_le_inv.mpr
    unfold anarchyValue anarchyValueFn
    have hp : 0 < ℓ x := lt_of_le_of_ne ((hL.2 ℓ hℓ).1.1 x hx.le) (Ne.symm hz)
    refine le_iSup_of_le ℓ (le_iSup_of_le hℓ (le_iSup_of_le x
      (le_iSup_of_le hx (le_iSup_of_le hp
        (le_iSup_of_le lam (le_iSup_of_le hlam (le_iSup_of_le hsolve ?_)))))))
    rw [ENNReal.ofReal_inv_of_pos (denominator_pos ℓ (hL.2 ℓ hℓ) x hx lam hlam hp)]

#print axioms solution
