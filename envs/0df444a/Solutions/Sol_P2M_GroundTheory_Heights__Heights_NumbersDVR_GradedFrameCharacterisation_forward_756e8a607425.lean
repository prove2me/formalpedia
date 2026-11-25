-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_forward_756e8a607425
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:07:12.5021+00:00
-- url     : https://prove2.me/submissions/1935faf9-0e7a-4364-bc2f-28bde9237015

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_coeff_eq_zero_of_tri_fd257542d139
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_mon_ne_zero_c2553a9ef5d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
variable {o : Type u} [CommRing o] {Ω : Type v} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type w}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}
  {w : Module.Basis (Fin N) Ω E} {b : Fin N → K → ℤ}
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
theorem _root_.solution (h : IsFlagFrame y B w b) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B
      (fun i => Submodule.span Ω (w '' {j | (j : ℕ) < i})) b w := by
  intro c hc
  have hm := mon_ne_zero (y := y) hc
  have hex : ∀ i, ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧
      w.repr v i = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) := by
    intro i
    have hmem : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) ∈ degLat o y (b i) c :=
      ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← h.graded c hc i] at hmem
    exact hmem
  choose bb hbb hup hdiag using hex
  have hd : ∀ q, w.repr (bb q) q ≠ 0 := fun q => by rw [hdiag q]; exact hm _
  have hli : LinearIndependent Ω bb := Fintype.linearIndependent_iff.mpr fun g hg q =>
    coeff_eq_zero_of_tri w bb hup hd g 0 (fun j _ => by rw [hg]; simp) q (Nat.zero_le _)
  have : FiniteDimensional Ω E := Module.Finite.of_basis w
  have hsp : Submodule.span Ω (Set.range bb) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_eq_card_basis w])

  have hgen : ∀ n : ℕ, ∀ e ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr e j = 0) →
      ∃ a : Fin N → Ω, (∀ q, a q ∈ chartRing o (segreVec y) c) ∧ e = ∑ q, a q • bb q := by
    intro n
    induction n with
    | zero =>
      intro e _ he
      refine ⟨0, fun _ => zero_mem _, ?_⟩
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      exact w.repr.injective (Finsupp.ext fun j => by simpa using he j (Nat.zero_le _))
    | succ n ih =>
      intro e he hz
      by_cases hn : n < N
      · have hmem : w.repr e ⟨n, hn⟩ ∈ degLat o y (b ⟨n, hn⟩) c := by
          rw [← h.graded c hc ⟨n, hn⟩]
          exact ⟨e, he, fun j hj => hz j (by rw [Fin.lt_def] at hj; simp at hj; omega), rfl⟩
        obtain ⟨a, ha, hae⟩ := hmem
        obtain ⟨a', ha', he'⟩ := ih (e - a • bb ⟨n, hn⟩)
          (sub_mem he (B.stable c a ha _ (hbb _))) (fun j hj => by
            rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
            rcases Nat.lt_or_ge n (j : ℕ) with hlt | hge
            · rw [hz j hlt, hup _ j (Fin.lt_def.mpr hlt), mul_zero, sub_zero]
            · have hj : j = ⟨n, hn⟩ := Fin.ext (le_antisymm hge hj)
              subst hj
              rw [hdiag, hae]
              simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon])
        refine ⟨a' + Pi.single ⟨n, hn⟩ a, fun q => add_mem (ha' q) ?_, ?_⟩
        · by_cases hq : q = ⟨n, hn⟩
          · subst hq; simpa using ha
          · simp [hq]
        · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
          rw [← he', Finset.sum_eq_single (⟨n, hn⟩ : Fin N)]
          · simp
          · intro q _ hq; simp [hq]
          · simp
      · exact ih e he fun j hj => absurd j.isLt (by omega)
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
  refine ⟨bb, hli, hsp, fun e => ⟨fun ⟨n, hn⟩ => ?_, fun ⟨a, ha, hae⟩ => ⟨0, ?_⟩⟩, fun i => ⟨1, ?_, ?_⟩⟩
  · rw [one_pow, one_smul] at hn
    obtain ⟨a, ha, hae⟩ := hgen N e hn (fun j hj => absurd j.isLt (by omega))
    exact ⟨a, fun q => ⟨0, by rw [pow_zero, one_mul]; exact ha q⟩, hae⟩
  · rw [pow_zero, one_smul, hae]
    refine AddSubgroup.sum_mem _ fun q _ => B.stable c _ ?_ _ (hbb q)
    obtain ⟨n, hn⟩ := ha q
    rwa [one_pow, one_mul] at hn
  · exact ⟨one_ne_zero, ⟨0, by rw [pow_zero, one_mul]; exact one_mem _⟩,
      ⟨0, by rw [pow_zero, one_mul, inv_one]; exact one_mem _⟩⟩
  · rw [Module.Basis.mem_span_image]
    intro j hj
    simp only [Set.mem_ofPred_eq, Fin.val_castSucc]
    rw [Finset.mem_coe, Finsupp.mem_support_iff, map_sub, map_smul, Module.Basis.repr_self,
      Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, one_mul] at hj
    by_contra hji
    rcases (not_lt.mp hji).lt_or_eq with hlt | heq
    · apply hj
      rw [hup i j (Fin.lt_def.mpr hlt), Finsupp.single_eq_of_ne (ne_of_gt (Fin.lt_def.mpr hlt)),
        mul_zero, sub_zero]
    · have hji' : j = i := Fin.ext heq.symm
      subst hji'
      apply hj
      rw [hdiag, Finsupp.single_eq_same, mul_one, sub_self]
end GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
