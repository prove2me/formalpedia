-- Prove2me | solution 1 for TPG.corollary_1_gamma_alpha_mixing
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:36:58.566226+00:00
-- url     : https://prove2.me/submissions/969c5cbe-ec98-4a54-990a-4ed12c8a1866

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference
import Theorems.Thm_TPG_lemma_2_alpha_mixing
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-- A coordinate inside the window `[a, b]` is measurable for the window sigma-algebra. -/
private lemma c1_measurable_coord {S : Type} [MeasurableSpace S] (T a b : ℕ) (u : Fin T)
    (hu : a ≤ (u : ℕ) ∧ (u : ℕ) ≤ b) :
    Measurable[sigmaWindow T a b] (fun ω : Traj S T => ω u) := by
  have hle : MeasurableSpace.comap (fun ω : Traj S T => ω u) inferInstance ≤ sigmaWindow T a b := by
    unfold sigmaWindow
    exact le_iSup₂ (f := fun (t : Fin T) (_ : a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b) =>
      MeasurableSpace.comap (fun ω : Traj S T => ω t) inferInstance) u hu
  exact (comap_measurable (fun ω : Traj S T => ω u)).mono hle le_rfl

/-- `Γ_t` is measurable for any window sigma-algebra containing the coordinates `t, …, t + k`. -/
private lemma c1_measurable_GammaTerm {S : Type} [MeasurableSpace S] (T k a b : ℕ) (t : Fin T)
    (hlo : a ≤ (t : ℕ)) (hhi : ∀ u : Fin T, (u : ℕ) ≤ (t : ℕ) + k → (u : ℕ) ≤ b) :
    Measurable[sigmaWindow T a b] (fun ω : Traj S T => GammaTerm k t ω) := by
  unfold GammaTerm
  have hZ : Measurable[sigmaWindow T a b] (fun ω : Traj S T => ipw (Z t ω)) := by
    have h1 : Measurable[sigmaWindow T a b] (fun ω : Traj S T => Z t ω) := by
      unfold Z
      exact (measurable_snd.fst).comp
        (c1_measurable_coord T a b t ⟨hlo, hhi t (Nat.le_add_right _ _)⟩)
    exact (Measurable.of_discrete (f := ipw)).comp h1
  refine Measurable.mul hZ ?_
  refine Finset.measurable_fun_sum _ fun u _ => ?_
  by_cases hu : (t : ℕ) ≤ (u : ℕ) ∧ (u : ℕ) ≤ (t : ℕ) + k
  · simp only [hu, and_self, if_true]
    unfold Y
    exact (measurable_snd.snd).comp
      (c1_measurable_coord T a b u ⟨le_trans hlo hu.1, hhi u hu.2⟩)
  · simp only [hu, if_false]
    exact measurable_const

private lemma c1_sigmaGamma_le {S : Type} [MeasurableSpace S] (T k a b a' b' : ℕ)
    (hlo : ∀ t : Fin T, a ≤ (t : ℕ) → a' ≤ (t : ℕ))
    (hhi : ∀ t u : Fin T, (t : ℕ) ≤ b → (u : ℕ) ≤ (t : ℕ) + k → (u : ℕ) ≤ b') :
    sigmaGamma S T k a b ≤ sigmaWindow T a' b' := by
  unfold sigmaGamma
  refine iSup_le fun t => iSup_le fun ht => ?_
  exact (c1_measurable_GammaTerm T k a' b' t (hlo t ht.1) (fun u hu => hhi t u ht.2 hu)).comap_le

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ γ M : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M)
    (s h : ℕ) (hsh : s + h + 1 < T)
    (A B : Set (Traj S T))
    (hA : MeasurableSet[sigmaGamma S T k 0 s] A)
    (hB : MeasurableSet[sigmaGamma S T k (s + h + 1) T] B) :
    |(E.expLaw T θ).real (A ∩ B) - (E.expLaw T θ).real A * (E.expLaw T θ).real B|
      ≤ γ ^ (h - k) := by
  rcases Nat.lt_or_ge k h with hkh | hkh
  · -- gap larger than the truncation: Lemma 2 with `s + k` and `h - k`
    have hA' : MeasurableSet[sigmaWindow T 0 (s + k)] A :=
      c1_sigmaGamma_le (S := S) T k 0 s 0 (s + k) (fun _ _ => Nat.zero_le _)
        (fun t u ht hu => by omega) A hA
    have hB' : MeasurableSet[sigmaWindow T (s + k + (h - k) + 1) T] B := by
      have he : s + k + (h - k) + 1 = s + h + 1 := by omega
      rw [he]
      exact c1_sigmaGamma_le (S := S) T k (s + h + 1) T (s + h + 1) T (fun _ ht => ht)
        (fun t u _ _ => u.2.le) B hB
    exact lemma_2_alpha_mixing E T θ γ M hθ0 hθ1 hγ0 hγ1 hmix hM (s + k) (h - k) (by omega)
      A B hA' hB'
  · -- gap at most the truncation: the bound is `1`
    have hzero : h - k = 0 := by omega
    rw [hzero, pow_zero]
    have hP : IsProbabilityMeasure (E.expLaw T θ) := by
      unfold Env.expLaw
      exact isProbabilityMeasure_trajLaw E T _ (fun _ => ⟨hθ0.le, hθ1.le⟩)
    have h1 : 0 ≤ (E.expLaw T θ).real (A ∩ B) := measureReal_nonneg
    have h2 : (E.expLaw T θ).real (A ∩ B) ≤ 1 := measureReal_le_one
    have h3 : 0 ≤ (E.expLaw T θ).real A := measureReal_nonneg
    have h4 : (E.expLaw T θ).real A ≤ 1 := measureReal_le_one
    have h5 : 0 ≤ (E.expLaw T θ).real B := measureReal_nonneg
    have h6 : (E.expLaw T θ).real B ≤ 1 := measureReal_le_one
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg h3 h5, mul_le_one₀ h4 h5 h6]
