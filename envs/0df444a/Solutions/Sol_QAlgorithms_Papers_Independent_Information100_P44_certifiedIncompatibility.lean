-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.certifiedIncompatibility
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:44:10.732303+00:00
-- url     : https://prove2.me/submissions/b542262b-3b89-46a9-a76b-c13898e9bfb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_certifiedSDPBounds
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_cgpCompactAttainment
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_concreteCGPNonempty
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_choiSDPEquivalence
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_thermalShellRepresentation
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_thermalGramConservation

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44

attribute [local instance] Classical.propDecidable

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

noncomputable def thermalKrausFlat {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) : Fin (b * b) → Mat d :=
  fun k => thermalKraus D (finProdFinEquiv.symm k)

lemma thermalKrausFlat_isKraus {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) : IsKrausFamily (thermalKrausFlat D) := by
  unfold IsKrausFamily
  have h := g52c_thermal_kraus D
  unfold IsKrausFamily at h
  have heq : ∑ k : Fin (b * b), (thermalKrausFlat D k)ᴴ * (thermalKrausFlat D k) =
      ∑ a : Fin b × Fin b, (thermalKraus D a)ᴴ * (thermalKraus D a) :=
    Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)
  rw [heq, h]

lemma thermalKrausFlat_apply {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) (X : Mat d) :
    krausApply (thermalKrausFlat D) X = thermalApply D X := by
  simp only [krausApply, thermalApply]
  exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)

def X7KForm {d m : ℕ} (J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : Fin m → Mat d) : Prop :=
  ∀ p q, J p q = ∑ k, K k p.1 p.2 * conj (K k q.1 q.2)

lemma X7_kraus_entry {d : ℕ} {κ : Type*} [Fintype κ] (K : κ → Mat d) (X : Mat d) (r s : Fin d) :
    krausApply K X r s = ∑ a, ∑ p, ∑ q, K a r p * X p q * conj (K a s q) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma X7_choi_kraus {d m : ℕ} (K : Fin m → Mat d) : X7KForm (choi (krausApply K)) K := by
  intro p q
  simp only [choi, X7_kraus_entry, matrixUnit, Matrix.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single p.2]
  · rw [Finset.sum_eq_single q.2]
    · simp
    · intro v _ hv; simp [Ne.symm hv]
    · simp
  · intro u _ hu; simp [Ne.symm hu]
  · simp

lemma X7_fromChoi_kraus {d m : ℕ} {J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} {K : Fin m → Mat d}
    (hJ : X7KForm J K) (X : Mat d) : fromChoi J X = krausApply K X := by
  have hJ' : ∀ p q, J p q = ∑ k, K k p.1 p.2 * conj (K k q.1 q.2) := hJ
  ext x y
  rw [X7_kraus_entry]
  simp only [fromChoi, hJ', Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

lemma X7_psd_of_KForm {d m : ℕ} {J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} {K : Fin m → Mat d}
    (hJ : X7KForm J K) : J.PosSemidef := by
  have : J = (Matrix.of fun (k : Fin m) (p : Fin d × Fin d) => conj (K k p.1 p.2))ᴴ *
      Matrix.of fun (k : Fin m) (p : Fin d × Fin d) => conj (K k p.1 p.2) := by
    ext p q
    rw [hJ, Matrix.mul_apply]
    simp
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma X7_TP_iff {d m : ℕ} {J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} {K : Fin m → Mat d}
    (hJ : X7KForm J K) :
    IsKrausFamily K ↔ ∀ u v, ∑ x, J (x,u) (x,v) = if u = v then 1 else 0 := by
  have hJ' : ∀ p q, J p q = ∑ k, K k p.1 p.2 * conj (K k q.1 q.2) := hJ
  have key : ∀ u v, (∑ k, (K k)ᴴ * K k) v u = ∑ x, J (x,u) (x,v) := by
    intro u v
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hJ', RCLike.star_def]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold IsKrausFamily
  constructor
  · intro h u v
    rw [← key, h, Matrix.one_apply]
    by_cases huv : v = u
    · subst huv; simp
    · simp [huv, Ne.symm huv]
  · intro h
    ext u v
    have := h v u
    rw [← key] at this
    rw [this, Matrix.one_apply]
    by_cases huv : u = v
    · subst huv; simp
    · simp [huv, Ne.symm huv]

lemma thermal_kraus_entry {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (X : Mat d) (r s : Fin d) :
    thermalApply D X r s = ∑ a : Fin b × Fin b, ∑ p, ∑ q,
      thermalKraus D a r p * X p q * conj (thermalKraus D a s q) := by
  simp only [thermalApply, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma thermal_matrixUnit_entry {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (x u y v : Fin d) :
    thermalApply D (matrixUnit u v) x y =
      ∑ a : Fin b × Fin b, thermalKraus D a x u * conj (thermalKraus D a y v) := by
  rw [thermal_kraus_entry]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [matrixUnit, Matrix.single_apply]
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · simp
    · intro q _ hq; simp [Ne.symm hq]
    · simp
  · intro p _ hp
    rw [Finset.sum_eq_zero]
    intro q _; simp [Ne.symm hp]
  · simp

lemma thermal_support_term {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (x u y v : Fin d) (a : Fin b × Fin b) (hne : E x - E u ≠ E y - E v) :
    thermalKraus D a x u * conj (thermalKraus D a y v) = 0 := by
  by_cases h1 : E u + D.bathEnergy a.1 = E x + D.bathEnergy a.2
  · have h2 : E v + D.bathEnergy a.1 ≠ E y + D.bathEnergy a.2 := by
      intro h; apply hne; linarith
    have hU : (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (y, a.2) (v, a.1) = 0 :=
      D.support y v a.2 a.1 h2
    simp [thermalKraus, hU]
  · have hU : (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (x, a.2) (u, a.1) = 0 :=
      D.support x u a.2 a.1 h1
    simp [thermalKraus, hU]

lemma thermal_choi_supp {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (x u y v : Fin d) (hne : E x - E u ≠ E y - E v) :
    choi (thermalApply D) (x, u) (y, v) = 0 := by
  change thermalApply D (matrixUnit u v) x y = 0
  rw [thermal_matrixUnit_entry]
  apply Finset.sum_eq_zero
  intro a _
  exact thermal_support_term D x u y v a hne

lemma shell_inner_zero {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (x y u : Fin d) (hne : E x ≠ E y) :
    inner ℂ (shellVector D y u) (shellVector D x u) = 0 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', shellVector]
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h1 h2 h2
  · exfalso; apply hne; linarith
  · simp
  · simp
  · simp

lemma thermal_choi_diag {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (beta : ℝ) (D : ThermalDilation E beta b)
    (x y u : Fin d) :
    choi (thermalApply D) (x, u) (y, u) = inner ℂ (shellVector D y u) (shellVector D x u) := by
  by_cases he : E x = E y
  · have heq : E u - E u = E x - E y := by rw [he, sub_self, sub_self]
    have hrep := (thermalShellRepresentation hd E beta D).2.1 u u x y heq
    change thermalApply D (matrixUnit u u) x y = _
    exact hrep
  · rw [thermal_choi_supp D x u y u (by intro h; apply he; linarith)]
    rw [shell_inner_zero D x y u he]

lemma thermal_choi_gibbs {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (beta : ℝ) (D : ThermalDilation E beta b)
    (x y : Fin d) :
    (∑ u, choi (thermalApply D) (x, u) (y, u) * (gibbsWeight E beta u : ℂ)) =
      if x = y then (gibbsWeight E beta x : ℂ) else 0 := by
  have hdiag : ∀ u, choi (thermalApply D) (x, u) (y, u) * (gibbsWeight E beta u : ℂ) =
      (gibbsWeight E beta u : ℂ) * inner ℂ (shellVector D y u) (shellVector D x u) := by
    intro u
    rw [thermal_choi_diag hd E beta D x y u, mul_comm]
  rw [Finset.sum_congr rfl (fun u _ => hdiag u)]
  exact (thermalGramConservation hd E beta D).2 x y

lemma to_feasible_implies_channel_feasible (Phi : Map 4) (hTO : FixedTOFeasible Phi) :
    FixedChannelFeasible Phi := by
  obtain ⟨⟨b, D, hD⟩, hPop⟩ := hTO
  have hPhiApply : ∀ X, Phi X = thermalApply D X := hD
  have hChoiPhi_thermal : choi Phi = choi (thermalApply D) := by
    ext p q; simp only [choi]; rw [hPhiApply]
  let K := thermalKrausFlat D
  have hPhiK : ∀ X, Phi X = krausApply K X := fun X => by
    rw [thermalKrausFlat_apply, ← hPhiApply]
  have hChoiPhi_K : choi Phi = choi (krausApply K) := by
    ext p q; simp only [choi]; rw [hPhiK]
  have hJK : X7KForm (choi Phi) K := by
    rw [hChoiPhi_K]; exact X7_choi_kraus K
  have hRec : ∀ X, fromChoi (choi Phi) X = Phi X := by
    intro X
    rw [X7_fromChoi_kraus hJK, ← hPhiK]
  have hChoiFeas : FixedChoiFeasible (choi Phi) := by
    refine ⟨X7_psd_of_KForm hJK, ?_, ?_, ?_, ?_⟩
    · exact (X7_TP_iff hJK).mp (thermalKrausFlat_isKraus D)
    · intro x y
      rw [hChoiPhi_thermal]
      exact thermal_choi_gibbs (by decide) fixedEnergy 1 D x y
    · intro x u y v hne
      rw [hChoiPhi_thermal]
      exact thermal_choi_supp D x u y v hne
    · rw [hRec fixedRho]
      exact hPop
  exact (choiSDPEquivalence.1 Phi).mpr ⟨hChoiFeas, hRec⟩

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution :
    (¬ ∃ Phi : Map 4, FixedChannelFeasible Phi ∧
      ∀ k : Fin 3, channelObjective k Phi = cgpOptimum k) ∧
    (¬ ∃ Phi : Map 4, FixedTOFeasible Phi ∧
      ∀ k : Fin 3, channelObjective k Phi = cgpOptimum k) := by
  have part1 : ¬ ∃ Phi : Map 4, FixedChannelFeasible Phi ∧
      ∀ k : Fin 3, channelObjective k Phi = cgpOptimum k := by
    rintro ⟨Phi, hFeas, hObj⟩
    have hEquiv := (choiSDPEquivalence.1 Phi).mp hFeas
    have hChoi : FixedChoiFeasible (choi Phi) := hEquiv.1
    have hRec : ∀ X, fromChoi (choi Phi) X = Phi X := hEquiv.2
    have hNonempty : ({J | FixedChoiFeasible J} : Set (Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)).Nonempty :=
      concreteCGPNonempty.2
    obtain ⟨J₀, hJ₀Feas, hJ₀Max⟩ := (cgpCompactAttainment.2 hNonempty).2
    set S := (fun J => ∑ k : Fin 3, channelObjective k (fromChoi J)) '' {J | FixedChoiFeasible J}
    have hBdd : BddAbove S := by
      refine ⟨∑ k : Fin 3, channelObjective k (fromChoi J₀), ?_⟩
      rintro y ⟨K, hK, rfl⟩
      exact hJ₀Max K hK
    have hMem : (∑ k : Fin 3, channelObjective k (fromChoi (choi Phi))) ∈ S :=
      ⟨choi Phi, hChoi, rfl⟩
    have hle : (∑ k : Fin 3, channelObjective k (fromChoi (choi Phi))) ≤ cgpSumOptimum :=
      le_csSup hBdd hMem
    have hObjEq : ∀ k : Fin 3, channelObjective k (fromChoi (choi Phi)) = cgpOptimum k := by
      intro k
      unfold channelObjective
      rw [hRec fixedRho, ← channelObjective, hObj k]
    have hsum : (∑ k : Fin 3, cgpOptimum k) ≤ cgpSumOptimum := by
      have heq : (∑ k : Fin 3, cgpOptimum k) = ∑ k : Fin 3, channelObjective k (fromChoi (choi Phi)) := by
        refine Finset.sum_congr rfl (fun k _ => (hObjEq k).symm)
      rw [heq]
      exact hle
    have h1 := certifiedSDPBounds.1
    have h2 := certifiedSDPBounds.2.2.1
    linarith
  refine ⟨part1, ?_⟩
  rintro ⟨Phi, hTO, hObj⟩
  exact part1 ⟨Phi, to_feasible_implies_channel_feasible Phi hTO, hObj⟩
