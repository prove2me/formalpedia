-- Prove2me | solution 1 for ProxGapTight.amp_coordinate_prob
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:23:08.7166+00:00
-- url     : https://prove2.me/submissions/1bdf1172-911a-474a-950a-d3a8dd110dba

import Mathlib
import Definitions.Def_ProxGapTight_Phi
import Definitions.Def_ProxGapTight_amp

section
set_option autoImplicit false

namespace ProxGapTight.Dev.AmpCoord

open Classical

/-- evaluation at a nonzero vector is surjective on functionals -/
lemma eval_surj {F E : Type} [Field F] [AddCommGroup E] [Module F E] (t : ℕ)
    (w : Fin t → E) (hw : w ≠ 0) :
    Function.Surjective (fun f : (Fin t → E) →ₗ[F] F => f w) := by
  have : w ∉ (⊥ : Submodule F (Fin t → E)) := by simpa using hw
  obtain ⟨f, hf, -⟩ := Submodule.exists_le_ker_of_notMem this
  intro c
  refine ⟨(c / f w) • f, ?_⟩
  simp [hf]

lemma card_ker_mul {F E : Type} [Field F] [Fintype F] [AddCommGroup E] [Module F E]
    [Finite E] (t : ℕ) (w : Fin t → E) (hw : w ≠ 0) :
    Nat.card ((Fin t → E) →ₗ[F] F) =
      Nat.card {f : (Fin t → E) →ₗ[F] F // f w = 0} * Fintype.card F := by
  let ev : ((Fin t → E) →ₗ[F] F) →ₗ[F] F := LinearMap.applyₗ w
  have hs : Function.Surjective ev := eval_surj t w hw
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker ev)]
  have e1 : Nat.card (((Fin t → E) →ₗ[F] F) ⧸ LinearMap.ker ev) = Fintype.card F := by
    rw [Nat.card_congr (LinearMap.quotKerEquivOfSurjective ev hs).toEquiv, Nat.card_eq_fintype_card]
  rw [e1]
  rfl

lemma card_ne {F E : Type} [Field F] [Fintype F] [AddCommGroup E] [Module F E]
    [Finite E] (t : ℕ) (w : Fin t → E) (hw : w ≠ 0) :
    (Nat.card {f : (Fin t → E) →ₗ[F] F // f w ≠ 0} : ℝ) =
      (Nat.card ((Fin t → E) →ₗ[F] F) : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) := by
  have hfin : Finite ((Fin t → E) →ₗ[F] F) :=
    Finite.of_injective (fun f : (Fin t → E) →ₗ[F] F => (f : (Fin t → E) → F))
      DFunLike.coe_injective
  haveI := Fintype.ofFinite ((Fin t → E) →ₗ[F] F)
  have h1 := card_ker_mul (F := F) t w hw
  have h2 : Nat.card {f : (Fin t → E) →ₗ[F] F // f w ≠ 0} +
      Nat.card {f : (Fin t → E) →ₗ[F] F // f w = 0} =
      Nat.card ((Fin t → E) →ₗ[F] F) := by
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl (fun f : (Fin t → E) →ₗ[F] F => f w = 0)] 
    have : Fintype.card {f : (Fin t → E) →ₗ[F] F // f w = 0} ≤ Fintype.card ((Fin t → E) →ₗ[F] F) :=
      Fintype.card_subtype_le _
    omega
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1' : (Nat.card ((Fin t → E) →ₗ[F] F) : ℝ) =
      (Nat.card {f : (Fin t → E) →ₗ[F] F // f w = 0} : ℝ) * Fintype.card F := by
    exact_mod_cast h1
  have h2' : (Nat.card {f : (Fin t → E) →ₗ[F] F // f w ≠ 0} : ℝ) +
      (Nat.card {f : (Fin t → E) →ₗ[F] F // f w = 0} : ℝ) =
      (Nat.card ((Fin t → E) →ₗ[F] F) : ℝ) := by exact_mod_cast h2
  field_simp
  nlinarith

lemma card_idx {n t : ℕ} {E : Type} [Zero E] [Fintype E] (v : Fin n → E) :
    (Fintype.card {i : Fin t → Fin n // (fun k => v (i k)) = 0} : ℝ) =
      ((n : ℝ) - hammingNorm v) ^ t := by
  have h : Fintype.card {i : Fin t → Fin n // (fun k => v (i k)) = 0} =
      (Finset.univ.filter (fun a => v a = 0)).card ^ t := by
    rw [show Fintype.card {i : Fin t → Fin n // (fun k => v (i k)) = 0} =
      (Fintype.piFinset fun _ : Fin t => Finset.univ.filter (fun a : Fin n => v a = 0)).card by
        rw [Fintype.card_subtype]
        congr 1
        ext i
        simp [funext_iff]]
    rw [Fintype.card_piFinset]
    simp
  have h3 : (Finset.univ.filter (fun a => v a = 0)).card + hammingNorm v = n := by
    unfold hammingNorm
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => v a = 0)
    simpa using this
  rw [h]
  have : ((Finset.univ.filter (fun a => v a = 0)).card : ℝ) = (n : ℝ) - hammingNorm v := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast h3
  push_cast
  rw [this]

end ProxGapTight.Dev.AmpCoord

namespace ProxGapTight

theorem chk_amp_coordinate_prob (F E : Type) [Field F] [Fintype F] [AddCommGroup E] [Module F E]
    [Fintype E] [DecidableEq E] (n t : ℕ) (hn : 0 < n) (ht : 1 ≤ t) (v : Fin n → E) :
    (Nat.card {ω : AmpSample F E n t // ω.2 (fun k => v (ω.1 k)) ≠ 0} : ℝ) /
        (Nat.card (AmpSample F E n t) : ℝ) =
      (1 - 1 / (Fintype.card F : ℝ)) * Phi t ((hammingNorm v : ℝ) / (n : ℝ)) := by
  classical
  have hfin : Finite ((Fin t → E) →ₗ[F] F) :=
    Finite.of_injective (fun f : (Fin t → E) →ₗ[F] F => (f : (Fin t → E) → F))
      DFunLike.coe_injective
  haveI := Fintype.ofFinite ((Fin t → E) →ₗ[F] F)
  set h : ℕ := Nat.card ((Fin t → E) →ₗ[F] F) with hh
  have hpos : 0 < h := Nat.card_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- decompose
  have e : {ω : AmpSample F E n t // ω.2 (fun k => v (ω.1 k)) ≠ 0} ≃
      Σ i : Fin t → Fin n, {f : (Fin t → E) →ₗ[F] F // f (fun k => v (i k)) ≠ 0} :=
    Equiv.subtypeProdEquivSigmaSubtype (fun (i : Fin t → Fin n) (f : (Fin t → E) →ₗ[F] F) =>
      f (fun k => v (i k)) ≠ 0)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hsum : ((∑ i : Fin t → Fin n, Fintype.card {f : (Fin t → E) →ₗ[F] F // f (fun k => v (i k)) ≠ 0} : ℕ) : ℝ) =
      (∑ i : Fin t → Fin n, if (fun k => v (i k)) = 0 then (0 : ℝ) else (h : ℝ) * (1 - 1 / (Fintype.card F : ℝ))) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · simp [hi]
    · rw [← Nat.card_eq_fintype_card]
      exact Dev.AmpCoord.card_ne t _ hi
  have hcard : (Nat.card (AmpSample F E n t) : ℝ) = (n : ℝ) ^ t * h := by
    rw [Nat.card_prod]
    simp [hh]
  have hnz : ((Finset.univ.filter (fun i : Fin t → Fin n => ¬ (fun k => v (i k)) = 0)).card : ℝ) =
      (n : ℝ) ^ t - ((n : ℝ) - hammingNorm v) ^ t := by
    have hc := Dev.AmpCoord.card_idx (t := t) v
    have h1 := Fintype.card_subtype_compl (fun i : Fin t → Fin n => (fun k => v (i k)) = 0)
    rw [Fintype.card_subtype] at h1
    have h2 : Fintype.card {i : Fin t → Fin n // (fun k => v (i k)) = 0} ≤ Fintype.card (Fin t → Fin n) :=
      Fintype.card_subtype_le _
    have h3 : Fintype.card (Fin t → Fin n) = n ^ t := by simp
    have h4 : (Finset.univ.filter (fun i : Fin t → Fin n => ¬ (fun k => v (i k)) = 0)).card + Fintype.card {i : Fin t → Fin n // (fun k => v (i k)) = 0} = n ^ t := by omega
    have h5 : (((Finset.univ.filter (fun i : Fin t → Fin n => ¬ (fun k => v (i k)) = 0)).card + Fintype.card {i : Fin t → Fin n // (fun k => v (i k)) = 0} : ℕ) : ℝ) = (n : ℝ) ^ t := by
      rw [h4]; push_cast; rfl
    push_cast at h5
    have hc' : (Fintype.card {i : Fin t → Fin n // (fun k => v (i k)) = 0} : ℝ) = ((n : ℝ) - hammingNorm v) ^ t := by
      convert hc
    linarith [hc']
  have hsum2 : (∑ i : Fin t → Fin n, if (fun k => v (i k)) = 0 then (0 : ℝ) else (h : ℝ) * (1 - 1 / (Fintype.card F : ℝ))) =
      ((n : ℝ) ^ t - ((n : ℝ) - hammingNorm v) ^ t) * ((h : ℝ) * (1 - 1 / (Fintype.card F : ℝ))) := by
    rw [← hnz, Finset.sum_ite]
    simp
  rw [hsum, hsum2, hcard]
  unfold Phi
  have hnt : (0 : ℝ) < (n : ℝ) ^ t := by positivity
  have hh' : (0 : ℝ) < h := by exact_mod_cast hpos
  have : ((n : ℝ) - hammingNorm v) ^ t = (n : ℝ) ^ t * (1 - (hammingNorm v : ℝ) / n) ^ t := by
    rw [← mul_pow]; congr 1; field_simp
  rw [this]
  field_simp

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_amp_coordinate_prob := @ProxGapTight.chk_amp_coordinate_prob
