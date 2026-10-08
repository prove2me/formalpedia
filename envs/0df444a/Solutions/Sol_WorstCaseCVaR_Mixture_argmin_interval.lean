-- Prove2me | solution 1 for WorstCaseCVaR.Mixture.argmin_interval
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T04:20:17.534674+00:00
-- url     : https://prove2.me/submissions/754eaa9f-cc47-4f5d-b0bb-dd78fec5d935

import Definitions.Def_WorstCaseCVaR_Mixture_Setting

section
set_option autoImplicit false
open MeasureTheory
open WorstCaseCVaR.Mixture
namespace MixtureCodex

lemma hinge_integrable {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : Integrable (f x) P) (α : ℝ) : Integrable (fun y ↦ max (f x y-α) 0) P :=
  (hf.sub (integrable_const α)).pos_part

lemma mixture_integrable {l m : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    (g : (Fin m → ℝ) → ℝ) (hg : ∀ i, Integrable g (P i)) (lam : Fin l → ℝ) :
    Integrable g (mixture P lam) := by
  unfold mixture
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (hg i).smul_measure ENNReal.ofReal_ne_top

lemma mixture_isProbability {l m : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (lam : Fin l → ℝ)
    (h : lam ∈ stdSimplex ℝ (Fin l)) : IsProbabilityMeasure (mixture P lam) := by
  constructor
  unfold mixture
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ h.1 i),h.2]
  simp

lemma mixture_hinge_integral {l m n : ℕ} (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (x : Fin n → ℝ) (hf : ∀ i, Integrable (f x) (P i)) (lam : Fin l → ℝ)
    (h : lam ∈ stdSimplex ℝ (Fin l)) (α : ℝ) :
    (∫ y, max (f x y-α) 0 ∂(mixture P lam)) =
      ∑ i, lam i * ∫ y, max (f x y-α) 0 ∂P i := by
  unfold mixture
  rw [integral_finsetSum_measure (fun i hi ↦
    (hinge_integrable (P i) f x (hf i) α).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_smul_measure,ENNReal.toReal_ofReal (h.1 i),smul_eq_mul]

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
open WorstCaseCVaR.Mixture
namespace MixtureCodex

lemma ru_convex {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) : ConvexOn ℝ Set.univ (ruFun P f β x) := by
  refine ⟨convex_univ,?_⟩
  intro a ha b hb u v hu hv huv
  simp only [smul_eq_mul]
  have hh : (fun y ↦ max (f x y-(u*a+v*b)) 0) ≤ᵐ[P]
      (fun y ↦ u*max (f x y-a) 0 + v*max (f x y-b) 0) := by
    apply Filter.Eventually.of_forall
    intro y
    apply max_le
    · calc
        _ = u*(f x y-a)+v*(f x y-b) := by linear_combination -(f x y)*huv
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hv)
    · exact add_nonneg (mul_nonneg hu (le_max_right _ _)) (mul_nonneg hv (le_max_right _ _))
  have hi := integral_mono_ae (hinge_integrable P f x hf (u*a+v*b))
    (((hinge_integrable P f x hf a).const_mul u).add ((hinge_integrable P f x hf b).const_mul v)) hh
  change (∫ y, max (f x y-(u*a+v*b)) 0 ∂P) ≤
    (∫ y, u*max (f x y-a) 0 + v*max (f x y-b) 0 ∂P) at hi
  rw [integral_add ((hinge_integrable P f x hf a).const_mul u)
    ((hinge_integrable P f x hf b).const_mul v),integral_const_mul,integral_const_mul] at hi
  have hc : 0 ≤ (1-β)⁻¹ := inv_nonneg.mpr (by linarith)
  have he := mul_le_mul_of_nonneg_left hi hc
  dsimp [ruFun]
  nlinarith [he]

lemma hinge_integral_difference {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : Integrable (f x) P) (a b : ℝ) :
    |(∫ y, max (f x y-a) 0 ∂P)-(∫ y, max (f x y-b) 0 ∂P)| ≤ |a-b| := by
  rw [← integral_sub (hinge_integrable P f x hf a) (hinge_integrable P f x hf b)]
  have hh : ∀ᵐ y ∂P, ‖max (f x y-a) 0-max (f x y-b) 0‖ ≤ |a-b| := by
    apply Filter.Eventually.of_forall
    intro y
    have he : (f x y-a)-(f x y-b) = b-a := by ring
    simpa only [Real.norm_eq_abs,he,abs_sub_comm] using
      abs_max_sub_max_le_abs (f x y-a) (f x y-b) 0
  simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const hh

lemma ru_continuous {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) : Continuous (ruFun P f β x) := by
  let c := (1-β)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (by linarith)
  let K : NNReal := ⟨1+c,by linarith⟩
  have hL : LipschitzWith K (ruFun P f β x) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [Real.dist_eq,Real.dist_eq]
    change |ruFun P f β x a-ruFun P f β x b| ≤ (1+c)*|a-b|
    have he : ruFun P f β x a-ruFun P f β x b =
        (a-b)+c*((∫ y, max (f x y-a) 0 ∂P)-(∫ y, max (f x y-b) 0 ∂P)) := by
      dsimp [ruFun,c]
      ring
    rw [he]
    calc
      _ ≤ |a-b|+|c*((∫ y, max (f x y-a) 0 ∂P)-(∫ y, max (f x y-b) 0 ∂P))| := abs_add_le _ _
      _ = |a-b|+c*|(∫ y, max (f x y-a) 0 ∂P)-(∫ y, max (f x y-b) 0 ∂P)| := by
        rw [abs_mul,abs_of_nonneg hc]
      _ ≤ (1+c)*|a-b| := by
        have hh := mul_le_mul_of_nonneg_left (hinge_integral_difference P f x hf a b) hc
        nlinarith [hh]
  exact hL.continuous

lemma ru_lower_bounds {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) (a : ℝ) :
    a ≤ ruFun P f β x a ∧
    (1-β)⁻¹*(∫ y, f x y ∂P)+(1-(1-β)⁻¹)*a ≤ ruFun P f β x a := by
  have hc : 0 ≤ (1-β)⁻¹ := inv_nonneg.mpr (by linarith)
  have hp : 0 ≤ ∫ y, max (f x y-a) 0 ∂P := integral_nonneg (fun y ↦ le_max_right _ _)
  have hle := integral_mono_ae (hf.sub (integrable_const a)) (hinge_integrable P f x hf a)
    (Filter.Eventually.of_forall (fun y ↦ le_max_left (f x y-a) 0))
  change (∫ y, f x y-a ∂P) ≤ (∫ y, max (f x y-a) 0 ∂P) at hle
  rw [integral_sub hf (integrable_const a)] at hle
  simp only [integral_const,probReal_univ,one_smul] at hle
  have hh := mul_le_mul_of_nonneg_left hle hc
  constructor <;> dsimp [ruFun] <;> nlinarith [mul_nonneg hc hp,hh]

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory Set
open WorstCaseCVaR.Mixture
namespace MixtureCodex

lemma ru_sublevel_compact {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) (t : ℝ) :
    IsCompact {a : ℝ | ruFun P f β x a ≤ t} := by
  let c := (1-β)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith)
  have he : c*(1-β) = 1 := inv_mul_cancel₀ (by linarith)
  have hcone : 1 < c := by nlinarith [mul_pos hc hβ0]
  let L := (c*(∫ y, f x y ∂P)-t)/(c-1)
  have hs : {a : ℝ | ruFun P f β x a ≤ t} ⊆ Icc L t := by
    intro a ha
    have hb := ru_lower_bounds P f β hβ1 x hf a
    refine ⟨?_,hb.1.trans ha⟩
    change (c*(∫ y, f x y ∂P)-t)/(c-1) ≤ a
    apply (div_le_iff₀ (by linarith)).mpr
    have hh : c*(∫ y, f x y ∂P)+(1-c)*a ≤ t := hb.2.trans ha
    nlinarith [hh]
  have hclosed : IsClosed {a : ℝ | ruFun P f β x a ≤ t} :=
    isClosed_Iic.preimage (ru_continuous P f β hβ1 x hf)
  exact isCompact_Icc.of_isClosed_subset hclosed hs

lemma ru_min_exists {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) :
    ∃ a : ℝ, IsMinOn (ruFun P f β x) univ a := by
  let A := {a : ℝ | ruFun P f β x a ≤ ruFun P f β x 0}
  have h0 : (0 : ℝ) ∈ A := by
    change ruFun P f β x 0 ≤ ruFun P f β x 0
    exact le_rfl
  have hc : IsCompact A := ru_sublevel_compact P f β hβ0 hβ1 x hf _
  obtain ⟨a,ha,hm⟩ := hc.exists_isMinOn ⟨0,h0⟩ (ru_continuous P f β hβ1 x hf).continuousOn
  refine ⟨a,isMinOn_iff.mpr ?_⟩
  intro b hb
  by_cases hba : b ∈ A
  · exact isMinOn_iff.mp hm b hba
  · exact (isMinOn_iff.mp hm 0 h0).trans (le_of_lt (lt_of_not_ge hba))

lemma argmin_interval_complete {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) :
    ∃ a b : ℝ, a ≤ b ∧ {α : ℝ | IsMinOn (ruFun P f β x) Set.univ α} = Set.Icc a b := by
  obtain ⟨q,hq⟩ := ru_min_exists P f β hβ0 hβ1 x hf
  let A := {a : ℝ | IsMinOn (ruFun P f β x) univ a}
  have he : A = {a : ℝ | ruFun P f β x a ≤ ruFun P f β x q} := by
    ext a
    constructor
    · intro ha
      exact isMinOn_iff.mp ha q (mem_univ q)
    · intro ha
      apply isMinOn_iff.mpr
      intro b hb
      exact ha.trans (isMinOn_iff.mp hq b hb)
  have hc : IsCompact A := by rw [he]; exact ru_sublevel_compact P f β hβ0 hβ1 x hf _
  have hne : A.Nonempty := ⟨q,hq⟩
  have hcv : Convex ℝ A := by
    rw [he]
    simpa only [mem_univ,true_and] using (ru_convex P f β hβ1 x hf).convex_le (ruFun P f β x q)
  have hi : A = Icc (sInf A) (sSup A) := eq_Icc_of_connected_compact (hcv.isConnected hne) hc
  have hab : sInf A ≤ sSup A := (csInf_le hc.bddBelow (hne.choose_spec)).trans
    (le_csSup hc.bddAbove hne.choose_spec)
  exact ⟨sInf A,sSup A,hab,hi⟩

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
theorem solution {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hf : Integrable (f x) P) :
    ∃ a b : ℝ, a ≤ b ∧ {α : ℝ | IsMinOn (ruFun P f β x) Set.univ α} = Set.Icc a b := by
  exact MixtureCodex.argmin_interval_complete P f β hβ0 hβ1 x hf

end

#print axioms solution
