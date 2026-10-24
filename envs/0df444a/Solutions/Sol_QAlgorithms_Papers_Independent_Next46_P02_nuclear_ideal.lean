-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P02.nuclear_ideal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:15:04.593751+00:00
-- url     : https://prove2.me/submissions/2390886f-1b98-44b0-8762-66d9b0652280

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Banach

variable {X Y V W : Type*}

variable [NormedAddCommGroup X] [NormedSpace F X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace F Y] [CompleteSpace Y]

variable [NormedAddCommGroup V] [NormedSpace F V] [CompleteSpace V]

variable [NormedAddCommGroup W] [NormedSpace F W] [CompleteSpace W]

lemma X7A14_rep_comp (T : X →L[F] Y) (R : V →L[F] X) (L : Y →L[F] W)
    (f : ℕ → (X →L[F] F)) (y : ℕ → Y) (h : BanachNuclearRepresentation T f y) :
    BanachNuclearRepresentation ((L.comp T).comp R) (fun k => (f k).comp R) (fun k => L (y k)) ∧
      ∑' k, ‖(f k).comp R‖ * ‖L (y k)‖ ≤ ‖L‖ * ‖R‖ * ∑' k, ‖f k‖ * ‖y k‖ := by
  obtain ⟨hs, hx⟩ := h
  have hle : ∀ k, ‖(f k).comp R‖ * ‖L (y k)‖ ≤ ‖L‖ * ‖R‖ * (‖f k‖ * ‖y k‖) := fun k => by
    have h1 : ‖(f k).comp R‖ ≤ ‖f k‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    have h2 : ‖L (y k)‖ ≤ ‖L‖ * ‖y k‖ := L.le_opNorm _
    calc ‖(f k).comp R‖ * ‖L (y k)‖ ≤ (‖f k‖ * ‖R‖) * (‖L‖ * ‖y k‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hs' : Summable (fun k => ‖(f k).comp R‖ * ‖L (y k)‖) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle (hs.mul_left _)
  refine ⟨⟨hs', fun v => ?_⟩, ?_⟩
  · have := (hx (R v)).map L L.continuous
    simpa [Function.comp_def, map_smul] using this
  · rw [← tsum_mul_left]
    exact hs'.tsum_le_tsum hle (hs.mul_left _)

lemma X7A14_nuclear_ideal
    (T : X →L[F] Y) (R : V →L[F] X) (L : Y →L[F] W)
    (hT : IsNuclear T) :
    IsNuclear ((L.comp T).comp R) ∧
      banachNuclearNorm ((L.comp T).comp R) ≤ ‖L‖ * banachNuclearNorm T * ‖R‖ := by
  obtain ⟨f, y, hrep⟩ := hT
  refine ⟨⟨_, _, (X7A14_rep_comp T R L f y hrep).1⟩, ?_⟩
  set K := ‖L‖ * ‖R‖ with hK
  have hK0 : 0 ≤ K := by positivity
  have e : ‖L‖ * banachNuclearNorm T * ‖R‖ = K • banachNuclearNorm T := by
    simp only [hK, smul_eq_mul]; ring
  rw [e]
  unfold banachNuclearNorm
  rw [← Real.sInf_smul_of_nonneg hK0]
  apply le_csInf
  · exact ⟨K • ∑' k, ‖f k‖ * ‖y k‖, ⟨_, ⟨f, y, hrep, rfl⟩, rfl⟩⟩
  · rintro _ ⟨c, ⟨f', y', hr, rfl⟩, rfl⟩
    obtain ⟨hr', hc⟩ := X7A14_rep_comp T R L f' y' hr
    refine le_trans (csInf_le ⟨0, ?_⟩ ⟨_, _, hr', rfl⟩) (by simpa [smul_eq_mul] using hc)
    rintro _ ⟨g, z, _, rfl⟩
    exact tsum_nonneg fun k => by positivity

end Banach

end QAlgorithms.Papers.Independent.Next46.P02

end

noncomputable section

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Banach

variable {X Y V W : Type*}

variable [NormedAddCommGroup X] [NormedSpace F X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace F Y] [CompleteSpace Y]

variable [NormedAddCommGroup V] [NormedSpace F V] [CompleteSpace V]

variable [NormedAddCommGroup W] [NormedSpace F W] [CompleteSpace W]

open QAlgorithms.Papers.Independent.Next46.P02 in
theorem solution [CompleteSpace X] [CompleteSpace Y] [CompleteSpace V] [CompleteSpace W]
    (T : X →L[F] Y) (R : V →L[F] X) (L : Y →L[F] W)
    (hT : IsNuclear T) :
    IsNuclear ((L.comp T).comp R) ∧
      banachNuclearNorm ((L.comp T).comp R) ≤ ‖L‖ * banachNuclearNorm T * ‖R‖ :=
  X7A14_nuclear_ideal T R L hT

end Banach

end
