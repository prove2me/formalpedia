-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P22.classical_transposeRecovery
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:07:01.250345+00:00
-- url     : https://prove2.me/submissions/62c74e19-0572-4c2b-9559-536d1f80b092

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open MeasureTheory ProbabilityTheory InformationTheory

theorem X7T_jointApply {α β : Type*} (μ : PMF α) (k : α → PMF β) (a : α) (b : β) :
    (μ.bind fun x => (k x).map (Prod.mk x)) (a, b) = μ a * k a b := by
  rw [PMF.bind_apply]
  rw [tsum_eq_single a]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single b]
    · simp
    · intro b' hb'
      simp [Ne.symm hb']
  · intro a' ha'
    rw [PMF.map_apply]
    have : ∀ b', ((a, b) = (a', b')) ↔ False := by
      intro b'; simp [Ne.symm ha']
    simp [Ne.symm ha']

theorem X7T_channelJointApply {X U : Type*} (q : PMF X) (t : X → PMF U) (x : X) (u : U) :
    channelJoint q t (x, u) = q x * t x u :=
  X7T_jointApply q t x u

theorem X7T_fiberMass {X U : Type*} (q : PMF X) (t : X → PMF U) (u : U) :
    ∑' xu : X × U, ({xu : X × U | xu.2 = u}.indicator (channelJoint q t)) xu = (q.bind t) u := by
  rw [ENNReal.tsum_prod', PMF.bind_apply]
  congr 1
  funext x
  rw [tsum_eq_single u]
  · simp [Set.indicator, X7T_channelJointApply]
  · intro u' hu'
    simp [Set.indicator, hu']

theorem X7T_transposeApply {X U : Type*} (q : PMF X) (t : X → PMF U) (u : U) (x : X)
    (h : (q.bind t) u ≠ 0) :
    transposeChannel q t u x = q x * t x u * ((q.bind t) u)⁻¹ := by
  have hex : ∃ xu ∈ {xu : X × U | xu.2 = u}, xu ∈ (channelJoint q t).support := by
    rw [PMF.bind_apply] at h
    obtain ⟨x0, hx0⟩ : ∃ x0, q x0 * t x0 u ≠ 0 := by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact h (by simp [hc])
    refine ⟨(x0, u), rfl, ?_⟩
    rw [PMF.mem_support_iff, X7T_channelJointApply]
    exact hx0
  unfold transposeChannel
  rw [dif_pos hex, PMF.map_apply, tsum_eq_single (x, u)]
  · simp only [if_true]
    rw [PMF.filter_apply, X7T_fiberMass]
    simp [Set.indicator, X7T_channelJointApply]
  · intro xu hxu
    by_cases h1 : x = xu.1
    · rw [if_pos h1, PMF.filter_apply]
      have : xu.2 ≠ u := by
        intro h2; apply hxu; ext <;> simp [h1, h2]
      simp [Set.indicator, this]
    · rw [if_neg h1]

theorem X7T_bayes {X U : Type*} (q : PMF X) (t : X → PMF U) (x : X) (u : U) :
    t x u * q x = transposeChannel q t u x * (q.bind t) u := by
  by_cases h : (q.bind t) u = 0
  · rw [h, mul_zero]
    rw [PMF.bind_apply] at h
    have := ENNReal.tsum_eq_zero.1 h x
    rw [mul_comm]; exact this
  · rw [X7T_transposeApply q t u x h, mul_assoc, ENNReal.inv_mul_cancel h (PMF.apply_ne_top _ _)]
    ring

theorem X7T_recover {X U : Type*} (q : PMF X) (t : X → PMF U) :
    (q.bind t).bind (transposeChannel q t) = q := by
  ext x
  rw [PMF.bind_apply]
  have : ∀ u, (q.bind t) u * transposeChannel q t u x = t x u * q x := by
    intro u; rw [X7T_bayes q t x u, mul_comm]
  simp_rw [this]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem X7T_swap {X U : Type*} (q : PMF X) (t : X → PMF U) :
    (channelJoint q t).map Prod.swap =
      (q.bind t).bind (fun u => (transposeChannel q t u).map (Prod.mk u)) := by
  ext ⟨u, x⟩
  rw [X7T_jointApply, PMF.map_apply, tsum_eq_single (x, u)]
  · simp only [Prod.swap_prod_mk, if_true]
    rw [X7T_channelJointApply, mul_comm ((q.bind t) u), ← X7T_bayes, mul_comm]
  · intro xu hxu
    have : (u, x) ≠ xu.swap := by
      intro h; apply hxu; rw [← Prod.swap_swap xu, ← h]; rfl
    simp [this]


section Meas
variable {α β : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]

def X7T_ker (k : α → PMF β) : Kernel α β := ⟨fun a => (k a).toMeasure, Measurable.of_discrete⟩

instance X7T_ker_markov (k : α → PMF β) : IsMarkovKernel (X7T_ker k) :=
  ⟨fun a => by change IsProbabilityMeasure (k a).toMeasure; infer_instance⟩

theorem X7T_toMeasure_sum (μ : PMF α) :
    μ.toMeasure = Measure.sum (fun a => μ a • Measure.dirac a) := by
  ext s hs
  rw [Measure.sum_apply _ hs, μ.toMeasure_apply hs]
  congr 1
  funext a
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul, Set.indicator]
  split_ifs <;> simp

theorem X7T_lint (μ : PMF α) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ.toMeasure = ∑' a, μ a * f a := by
  rw [X7T_toMeasure_sum, lintegral_sum_measure]
  congr 1
  funext a
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

theorem X7T_compProd (μ : PMF α) (k : α → PMF β) :
    μ.toMeasure ⊗ₘ X7T_ker k = (μ.bind fun a => (k a).map (Prod.mk a)).toMeasure := by
  ext s hs
  rw [Measure.compProd_apply hs, X7T_lint, PMF.toMeasure_apply _ hs, ENNReal.tsum_prod']
  congr 1
  funext a
  change μ a * (k a).toMeasure (Prod.mk a ⁻¹' s) = _
  rw [PMF.toMeasure_apply _ (measurable_prodMk_left hs), ← ENNReal.tsum_mul_left]
  congr 1
  funext b
  simp only [Set.indicator, Set.mem_preimage, X7T_jointApply]
  split_ifs <;> simp

end Meas

section Core
variable {X U : Type*} [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace U] [DiscreteMeasurableSpace U]

theorem X7T_swapMeasure (q : PMF X) (t : X → PMF U) :
    (channelJoint q t).toMeasure.map Prod.swap =
      (q.bind t).toMeasure ⊗ₘ X7T_ker (transposeChannel q t) := by
  rw [PMF.toMeasure_map (hf := measurable_swap), X7T_swap, X7T_compProd]

theorem X7T_jointMeasure (q : PMF X) (t : X → PMF U) :
    q.toMeasure ⊗ₘ X7T_ker t = (channelJoint q t).toMeasure := by
  rw [X7T_compProd]; rfl

theorem X7T_sndMeasure (P : PMF U) (r : U → PMF X) :
    (P.toMeasure ⊗ₘ X7T_ker r).map Prod.snd = (P.bind r).toMeasure := by
  rw [X7T_compProd, PMF.toMeasure_map (hf := measurable_snd), PMF.map_bind]
  have : (fun a => PMF.map Prod.snd (PMF.map (Prod.mk a) (r a))) = r := by
    funext u
    rw [PMF.map_comp]
    exact PMF.map_id _
  rw [this]

theorem X7T_chain (p q : PMF X) (t : X → PMF U) :
    klDiv p.toMeasure q.toMeasure ≥
      klDiv (p.bind t).toMeasure (q.bind t).toMeasure +
        klDiv ((p.bind t).toMeasure ⊗ₘ X7T_ker (transposeChannel p t))
          ((p.bind t).toMeasure ⊗ₘ X7T_ker (transposeChannel q t)) := by
  rw [← klDiv_compProd_eq_add, ← X7T_swapMeasure, ← X7T_swapMeasure,
    ← klDiv_compProd_left p.toMeasure q.toMeasure (X7T_ker t), X7T_jointMeasure, X7T_jointMeasure]
  exact klDiv_map_le _ _ measurable_swap

theorem X7T_chain_eq (p q : PMF X) (t : X → PMF U) :
    klDiv p.toMeasure q.toMeasure =
      klDiv (p.bind t).toMeasure (q.bind t).toMeasure +
        klDiv ((p.bind t).toMeasure ⊗ₘ X7T_ker (transposeChannel p t))
          ((p.bind t).toMeasure ⊗ₘ X7T_ker (transposeChannel q t)) := by
  refine le_antisymm ?_ (X7T_chain p q t)
  rw [← klDiv_compProd_eq_add, ← X7T_swapMeasure, ← X7T_swapMeasure,
    ← klDiv_compProd_left p.toMeasure q.toMeasure (X7T_ker t), X7T_jointMeasure, X7T_jointMeasure]
  have hs : ∀ m : Measure (X × U), (m.map Prod.swap).map Prod.swap = m := by
    intro m
    rw [Measure.map_map measurable_swap measurable_swap]
    simp
  calc klDiv (channelJoint p t).toMeasure (channelJoint q t).toMeasure
      = klDiv (((channelJoint p t).toMeasure.map Prod.swap).map Prod.swap)
          (((channelJoint q t).toMeasure.map Prod.swap).map Prod.swap) := by rw [hs, hs]
    _ ≤ _ := klDiv_map_le _ _ measurable_swap

theorem X7T_core (p q : PMF X) (t : X → PMF U) :
    klDiv (p.bind t).toMeasure (q.bind t).toMeasure +
      klDiv p.toMeasure ((p.bind t).bind (transposeChannel q t)).toMeasure ≤
        klDiv p.toMeasure q.toMeasure := by
  refine le_trans ?_ (X7T_chain p q t)
  gcongr
  have e : ((p.bind t).toMeasure ⊗ₘ X7T_ker (transposeChannel p t)).map Prod.snd = p.toMeasure := by
    rw [X7T_sndMeasure, X7T_recover]
  rw [← X7T_sndMeasure (p.bind t) (transposeChannel q t)]
  conv_lhs => rw [← e]
  exact klDiv_map_le _ _ measurable_snd

theorem X7T_det (p q : PMF X) (t : X → PMF U) (f : X → U) (hf : ∀ x, t x = PMF.pure (f x)) :
    klDiv p.toMeasure q.toMeasure ≤
      klDiv (p.bind t).toMeasure (q.bind t).toMeasure +
        klDiv p.toMeasure ((p.bind t).bind (transposeChannel q t)).toMeasure := by
  by_cases hac : ∃ u, (q.bind t) u = 0 ∧ (p.bind t) u ≠ 0
  · obtain ⟨u, hq, hp⟩ := hac
    have htop : klDiv (p.bind t).toMeasure (q.bind t).toMeasure = ⊤ := by
      apply klDiv_of_not_ac
      intro h
      have h1 : (q.bind t).toMeasure {u} = 0 := by
        rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.of_discrete)]; exact hq
      have h2 := h h1
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.of_discrete)] at h2
      exact hp h2
    rw [htop, top_add]; exact le_top
  · simp only [not_exists, not_and, not_not] at hac
    have hz : ∀ u x, u ≠ f x → (p.bind t) u * transposeChannel q t u x = 0 := by
      intro u x hu
      by_cases h : (q.bind t) u = 0
      · rw [hac u h, zero_mul]
      · rw [X7T_transposeApply q t u x h, hf x, PMF.pure_apply, if_neg hu]; simp
    have e1 : ((p.bind t).bind fun u => (transposeChannel p t u).map (Prod.mk u)) =
        p.map (fun x => (f x, x)) := by
      ext ⟨u, x⟩
      rw [X7T_jointApply, mul_comm, ← X7T_bayes, hf x, PMF.pure_apply, PMF.map_apply,
        tsum_eq_single x]
      · by_cases hu : u = f x
        · simp [hu]
        · simp [hu]
      · intro b hb
        have : (u, x) ≠ (f b, b) := by
          intro h; apply hb; exact (congrArg Prod.snd h).symm
        simp [this]
    have e2 : ((p.bind t).bind fun u => (transposeChannel q t u).map (Prod.mk u)) =
        ((p.bind t).bind (transposeChannel q t)).map (fun x => (f x, x)) := by
      ext ⟨u, x⟩
      rw [X7T_jointApply, PMF.map_apply, tsum_eq_single x]
      · by_cases hu : u = f x
        · subst hu
          rw [if_pos rfl]
          conv_rhs => rw [PMF.bind_apply]
          rw [tsum_eq_single (f x)]
          intro u' hu'
          exact hz u' x hu'
        · rw [hz u x hu]
          have : (u, x) ≠ (f x, x) := by
            intro h; exact hu (congrArg Prod.fst h)
          simp [this]
      · intro b hb
        have : (u, x) ≠ (f b, b) := by
          intro h; apply hb; exact (congrArg Prod.snd h).symm
        simp [this]
    rw [X7T_chain_eq p q t]
    gcongr
    rw [X7T_compProd, X7T_compProd, e1, e2,
      ← PMF.toMeasure_map (hf := (Measurable.of_discrete : Measurable (fun x : X => (f x, x)))),
      ← PMF.toMeasure_map (hf := (Measurable.of_discrete : Measurable (fun x : X => (f x, x))))]
    exact klDiv_map_le _ _ Measurable.of_discrete

end Core

end QAlgorithms.Papers.Independent.Gap48.P22

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)

open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)

open QAlgorithms.Entanglement (IsSeparableDensity)

open QAlgorithms.Papers.Independent.Gap48.P22 in
theorem solution {X U : Type*} (q : PMF X) (t : X → PMF U) :
    let r := transposeChannel q t
    (q.bind t).bind r = q ∧
      (∀ x u, t x u * q x = r u x * (q.bind t) u) ∧
      ∀ p : PMF X,
        discreteKL (p.bind t) (q.bind t) + discreteKL p ((p.bind t).bind r) ≤ discreteKL p q ∧
        ((∃ f : X → U, ∀ x, t x = PMF.pure (f x)) →
          discreteKL p q = discreteKL (p.bind t) (q.bind t) +
            discreteKL p ((p.bind t).bind r)) := by
  intro r
  letI : MeasurableSpace X := ⊤
  letI : MeasurableSpace U := ⊤
  have hle : ∀ p : PMF X,
      discreteKL (p.bind t) (q.bind t) + discreteKL p ((p.bind t).bind r) ≤ discreteKL p q := by
    intro p
    simp only [discreteKL]
    rw [ENNReal.div_add_div_same]
    exact ENNReal.div_le_div_right (X7T_core p q t) _
  refine ⟨X7T_recover q t, fun x u => X7T_bayes q t x u, fun p => ⟨hle p, ?_⟩⟩
  rintro ⟨f, hf⟩
  refine le_antisymm ?_ (hle p)
  simp only [discreteKL]
  rw [ENNReal.div_add_div_same]
  exact ENNReal.div_le_div_right (X7T_det p q t f hf) _

end
