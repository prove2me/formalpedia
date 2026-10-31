-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.conditionalTOUpgrade
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:39:25.469144+00:00
-- url     : https://prove2.me/submissions/7a544869-d70f-4b2b-9ff3-353acb13eb4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_certifiedSDPBounds
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_cgpCompactAttainment
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_concreteCGPNonempty
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_choiSDPEquivalence
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_thermalShellRepresentation
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_thermalGramConservation

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44
open scoped ComplexConjugate ComplexOrder Matrix BigOperators

theorem g52c_gibbs_sum {b : ℕ} (hb : 0 < b) (e : Fin b → ℝ) (beta : ℝ) :
    ∑ m, gibbsWeight e beta m = 1 := by
  simp only [gibbsWeight]
  rw [← Finset.sum_div, div_self]
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  exact (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty).ne'

theorem g52c_thermal_kraus {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) : IsKrausFamily (thermalKraus D) := by
  have hU : star (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) * D.U = 1 :=
    Unitary.star_mul_self_of_mem D.U.2
  rw [Matrix.star_eq_conjTranspose] at hU
  have hUe : ∀ (i j : Fin d) (m : Fin b),
      ∑ r, ∑ n, star ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, n) (i, m)) *
        (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, n) (j, m) =
        if i = j then 1 else 0 := by
    intro i j m
    have := congrFun (congrFun hU (i, m)) (j, m)
    rw [Matrix.mul_apply, Fintype.sum_prod_type] at this
    simp only [Matrix.conjTranspose_apply] at this
    rw [this, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h]
  unfold IsKrausFamily
  ext i j
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, thermalKraus, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  have hw : ∀ m : Fin b, ((Real.sqrt (gibbsWeight D.bathEnergy beta m) : ℂ)) *
      (Real.sqrt (gibbsWeight D.bathEnergy beta m) : ℂ) = (gibbsWeight D.bathEnergy beta m : ℂ) := by
    intro m
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt]
    simp only [gibbsWeight]
    exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le))
  have step : ∀ m : Fin b, ∑ n, ∑ r,
      (Real.sqrt (gibbsWeight D.bathEnergy beta m) : ℂ) *
        (starRingEnd ℂ) ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, n) (i, m)) *
      ((Real.sqrt (gibbsWeight D.bathEnergy beta m) : ℂ) *
        (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, n) (j, m)) =
      (gibbsWeight D.bathEnergy beta m : ℂ) * (if i = j then 1 else 0) := by
    intro m
    rw [← hUe i j m, Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [← hw m]; simp only [Complex.star_def]; ring
  rw [Finset.sum_congr rfl (fun m _ => step m), ← Finset.sum_mul]
  have hs : ∑ m, (gibbsWeight D.bathEnergy beta m : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, g52c_gibbs_sum D.bathPositive, Complex.ofReal_one]
  rw [hs, one_mul, Matrix.one_apply]

lemma X7_kraus_entry {d : ℕ} {κ : Type*} [Fintype κ] (K : κ → Mat d) (X : Mat d) (r s : Fin d) :
    krausApply K X r s = ∑ a, ∑ p, ∑ q, K a r p * X p q * conj (K a s q) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma X7_choi_kraus {d : ℕ} {κ : Type*} [Fintype κ] (K : κ → Mat d) (p q : Fin d × Fin d) :
    choi (krausApply K) p q = ∑ k, K k p.1 p.2 * conj (K k q.1 q.2) := by
  simp only [choi, X7_kraus_entry, matrixUnit, Matrix.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single p.2]
  · rw [Finset.sum_eq_single q.2]
    · simp
    · intro v _ hv; simp [Ne.symm hv]
    · simp
  · intro u _ hu; simp [Ne.symm hu]
  · simp

lemma X7_fromChoi_kraus {d : ℕ} {κ : Type*} [Fintype κ] (K : κ → Mat d) (X : Mat d) :
    fromChoi (choi (krausApply K)) X = krausApply K X := by
  ext x y
  rw [X7_kraus_entry]
  simp only [fromChoi, X7_choi_kraus, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

lemma X7_psd_of_kraus {d : ℕ} {κ : Type*} [Fintype κ] (K : κ → Mat d) :
    (choi (krausApply K)).PosSemidef := by
  have : choi (krausApply K) = (Matrix.of fun (k : κ) (p : Fin d × Fin d) => conj (K k p.1 p.2))ᴴ *
      Matrix.of fun (k : κ) (p : Fin d × Fin d) => conj (K k p.1 p.2) := by
    ext p q
    rw [X7_choi_kraus, Matrix.mul_apply]
    simp
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma X7_TP_of_kraus {d : ℕ} {κ : Type*} [Fintype κ] (K : κ → Mat d) (hK : IsKrausFamily K) (u v : Fin d) :
    ∑ x, choi (krausApply K) (x,u) (x,v) = if u = v then 1 else 0 := by
  have key : ∀ u v, (∑ k, (K k)ᴴ * K k) v u = ∑ x, choi (krausApply K) (x,u) (x,v) := by
    intro u v
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, X7_choi_kraus, RCLike.star_def]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [← key, show ∑ k, (K k)ᴴ * K k = 1 from hK, Matrix.one_apply]
  by_cases huv : u = v
  · subst huv; simp
  · rw [if_neg (Ne.symm huv), if_neg huv]

lemma thermal_choi_support {b : ℕ} (D : ThermalDilation fixedEnergy 1 b)
    (x u y v : Fin 4) (hne : fixedEnergy x - fixedEnergy u ≠ fixedEnergy y - fixedEnergy v) :
    choi (thermalApply D) (x, u) (y, v) = 0 := by
  change choi (krausApply (thermalKraus D)) (x, u) (y, v) = 0
  rw [X7_choi_kraus]
  apply Finset.sum_eq_zero
  intro a _
  by_cases h1 : fixedEnergy u + D.bathEnergy a.1 = fixedEnergy x + D.bathEnergy a.2
  · have h2 : fixedEnergy v + D.bathEnergy a.1 ≠ fixedEnergy y + D.bathEnergy a.2 := by
      intro h2
      apply hne
      linarith
    have hU : (D.U : Matrix (Fin 4 × Fin b) (Fin 4 × Fin b) ℂ) (y, a.2) (v, a.1) = 0 :=
      D.support y v a.2 a.1 h2
    have hK : thermalKraus D a y v = 0 := by
      simp [thermalKraus, hU]
    simp [hK]
  · have hU : (D.U : Matrix (Fin 4 × Fin b) (Fin 4 × Fin b) ℂ) (x, a.2) (u, a.1) = 0 :=
      D.support x u a.2 a.1 h1
    have hK : thermalKraus D a x u = 0 := by
      simp [thermalKraus, hU]
    simp [hK]

lemma thermal_choi_gibbs {b : ℕ} (D : ThermalDilation fixedEnergy 1 b) (x y : Fin 4) :
    (∑ u, choi (thermalApply D) (x, u) (y, u) * (gibbsWeight fixedEnergy 1 u : ℂ)) =
      if x = y then (gibbsWeight fixedEnergy 1 x : ℂ) else 0 := by
  by_cases hE : fixedEnergy x = fixedEnergy y
  · have hrep : ∀ u : Fin 4, choi (thermalApply D) (x, u) (y, u) =
        inner ℂ (shellVector D y u) (shellVector D x u) := by
      intro u
      change thermalApply D (matrixUnit u u) x y = _
      have heq : fixedEnergy u - fixedEnergy u = fixedEnergy x - fixedEnergy y := by
        simp [hE]
      exact (thermalShellRepresentation (by decide) fixedEnergy 1 D).2.1 u u x y heq
    have hgram := (thermalGramConservation (by decide) fixedEnergy 1 D).2 x y
    simp_rw [hrep]
    have : (∑ u, inner ℂ (shellVector D y u) (shellVector D x u) * (gibbsWeight fixedEnergy 1 u : ℂ)) =
        ∑ u, (gibbsWeight fixedEnergy 1 u : ℂ) * inner ℂ (shellVector D y u) (shellVector D x u) := by
      apply Finset.sum_congr rfl; intro u _; ring
    rw [this, hgram]
  · have hzero : ∀ u : Fin 4, choi (thermalApply D) (x, u) (y, u) = 0 := by
      intro u
      apply thermal_choi_support D x u y u
      intro h
      have : fixedEnergy x = fixedEnergy y := by linarith
      exact hE this
    simp_rw [hzero, zero_mul, Finset.sum_const_zero]
    rw [if_neg]
    rintro rfl
    exact hE rfl

lemma fixedTOFeasible_imp_choi (Phi : Map 4) (hPhi : FixedTOFeasible Phi) :
    FixedChoiFeasible (choi Phi) ∧ (∀ X, fromChoi (choi Phi) X = Phi X) := by
  obtain ⟨⟨b, D, hD⟩, hpop⟩ := hPhi
  have hPhiD : Phi = thermalApply D := funext hD
  subst hPhiD
  have hrec : ∀ X, fromChoi (choi (thermalApply D)) X = thermalApply D X :=
    X7_fromChoi_kraus (thermalKraus D)
  refine ⟨⟨X7_psd_of_kraus (thermalKraus D),
           X7_TP_of_kraus (thermalKraus D) (g52c_thermal_kraus D),
           thermal_choi_gibbs D,
           fun x u y v hne => thermal_choi_support D x u y v hne,
           ?_⟩, hrec⟩
  rw [hrec fixedRho]
  exact hpop

lemma choi_sum_le_cgpSumOptimum (K : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (hK : FixedChoiFeasible K) :
    ∑ k : Fin 3, channelObjective k (fromChoi K) ≤ cgpSumOptimum := by
  unfold cgpSumOptimum
  obtain ⟨J_max, hJ_max, hle⟩ := (cgpCompactAttainment.2 concreteCGPNonempty.2).2
  have hbdd : BddAbove ((fun J => ∑ k : Fin 3, channelObjective k (fromChoi J)) '' {J | FixedChoiFeasible J}) := by
    refine ⟨∑ k : Fin 3, channelObjective k (fromChoi J_max), ?_⟩
    rintro x ⟨J, hJ, rfl⟩
    exact hle J hJ
  exact le_csSup hbdd ⟨K, hK, rfl⟩

lemma to_sum_le_cgpSumOptimum (Phi : Map 4) (hPhi : FixedTOFeasible Phi) :
    ∑ k : Fin 3, channelObjective k Phi ≤ cgpSumOptimum := by
  obtain ⟨hchoi, hrec⟩ := fixedTOFeasible_imp_choi Phi hPhi
  have heq : ∑ k : Fin 3, channelObjective k Phi = ∑ k : Fin 3, channelObjective k (fromChoi (choi Phi)) := by
    simp only [channelObjective, hrec fixedRho]
  rw [heq]
  exact choi_sum_le_cgpSumOptimum (choi Phi) hchoi

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution
    (hbridge : ∀ k : Fin 3, toOptimum k = (cgpOptimum k : EReal)) :
    toSumOptimum < ∑ k : Fin 3, toOptimum k ∧
    ¬ ∃ Phi : Map 4, FixedTOFeasible Phi ∧
      ∀ k : Fin 3, (channelObjective k Phi : EReal) = toOptimum k := by
  have hbounds := certifiedSDPBounds
  have hgap : cgpSumOptimum < ∑ k : Fin 3, cgpOptimum k := by
    linarith [hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2]
  constructor
  · have hto_le : toSumOptimum ≤ (cgpSumOptimum : EReal) := by
      unfold toSumOptimum
      apply sSup_le
      rintro b ⟨Phi, hPhi, rfl⟩
      rw [EReal.coe_le_coe_iff]
      exact to_sum_le_cgpSumOptimum Phi hPhi
    have hsum_eq : ∑ k : Fin 3, toOptimum k = ((∑ k : Fin 3, cgpOptimum k : ℝ) : EReal) := by
      simp only [hbridge, Fin.sum_univ_three, ← EReal.coe_add]
    rw [hsum_eq]
    exact hto_le.trans_lt (EReal.coe_lt_coe_iff.mpr hgap)
  · rintro ⟨Phi, hPhi, hopt⟩
    have hsum_eq : ∑ k : Fin 3, cgpOptimum k = ∑ k : Fin 3, channelObjective k Phi := by
      have : ∀ k : Fin 3, (cgpOptimum k : EReal) = (channelObjective k Phi : EReal) := by
        intro k
        rw [← hbridge k, ← hopt k]
      have hreal : ∀ k : Fin 3, cgpOptimum k = channelObjective k Phi := by
        intro k
        exact EReal.coe_eq_coe_iff.mp (this k)
      exact Finset.sum_congr rfl (fun k _ => hreal k)
    have hle := to_sum_le_cgpSumOptimum Phi hPhi
    rw [← hsum_eq] at hle
    linarith
