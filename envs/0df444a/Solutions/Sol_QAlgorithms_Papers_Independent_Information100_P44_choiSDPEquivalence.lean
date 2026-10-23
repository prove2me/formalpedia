-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.choiSDPEquivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:09:00.790712+00:00
-- url     : https://prove2.me/submissions/906f8d25-f667-4307-a311-031cf97bcce6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

lemma X7_kraus_entry {d : ℕ} {κ : Type*} [Fintype κ] (K : κ → Mat d) (X : Mat d) (r s : Fin d) :
    krausApply K X r s = ∑ a, ∑ p, ∑ q, K a r p * X p q * conj (K a s q) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/-- `J` is the Choi matrix of the Kraus family `K`. -/
def X7KForm {d m : ℕ} (J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : Fin m → Mat d) : Prop :=
  ∀ p q, J p q = ∑ k, K k p.1 p.2 * conj (K k q.1 q.2)

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

lemma X7_choi_fromChoi {d : ℕ} (J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    choi (fromChoi J) = J := by
  ext p q
  simp only [choi, fromChoi, matrixUnit, Matrix.single_apply]
  rw [Finset.sum_eq_single p.2]
  · rw [Finset.sum_eq_single q.2]
    · simp
    · intro v _ hv; simp [Ne.symm hv]
    · simp
  · intro u _ hu
    apply Finset.sum_eq_zero; intro v _; simp [Ne.symm hu]
  · simp

lemma X7_psd_of_KForm {d m : ℕ} {J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} {K : Fin m → Mat d}
    (hJ : X7KForm J K) : J.PosSemidef := by
  have : J = (Matrix.of fun (k : Fin m) (p : Fin d × Fin d) => conj (K k p.1 p.2))ᴴ *
      Matrix.of fun (k : Fin m) (p : Fin d × Fin d) => conj (K k p.1 p.2) := by
    ext p q
    rw [hJ, Matrix.mul_apply]
    simp
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma X7_KForm_of_psd {d : ℕ} {J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hJ : J.PosSemidef) :
    ∃ (m : ℕ) (K : Fin m → Mat d), X7KForm J K := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hJ.nonneg
  let e := Fintype.equivFin (Fin d × Fin d)
  refine ⟨Fintype.card (Fin d × Fin d), fun k x u => conj (B (e.symm k) (x, u)), ?_⟩
  intro p q
  rw [hB, Matrix.mul_apply]
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.star_apply]

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
    by_cases huv : u = v
    · subst huv; simp
    · rw [if_neg (Ne.symm huv), if_neg huv]
  · intro h
    ext v u
    rw [key, h, Matrix.one_apply]
    by_cases huv : u = v
    · subst huv; simp
    · rw [if_neg (Ne.symm huv), if_neg huv]

lemma X7_diag {d : ℕ} (J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (f : Fin d → ℂ) (x y : Fin d) :
    fromChoi J (Matrix.diagonal f) x y = ∑ u, J (x,u) (y,u) * f u := by
  simp only [fromChoi, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_eq_single u]
  · simp
  · intro v _ hv; simp [Ne.symm hv]
  · simp

lemma X7_gibbs_iff {d : ℕ} (E : Fin d → ℝ) (beta : ℝ) (J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    fromChoi J (gibbsDensity E beta) = gibbsDensity E beta ↔
      ∀ x y, (∑ u, J (x,u) (y,u) * (gibbsWeight E beta u : ℂ)) =
        if x = y then (gibbsWeight E beta x : ℂ) else 0 := by
  unfold gibbsDensity
  rw [← Matrix.ext_iff]
  simp only [X7_diag, Matrix.diagonal_apply]

lemma X7_exp_ne {a b : ℝ} (h : a ≠ b) :
    ∃ t : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (a : ℂ)) ≠ Complex.exp (-Complex.I * (t : ℂ) * (b : ℂ)) := by
  refine ⟨Real.pi / (b - a), fun heq => ?_⟩
  have hba : (b : ℂ) - a ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (Ne.symm h)
  have h1 : Complex.exp (-Complex.I * ((Real.pi / (b - a) : ℝ) : ℂ) * (a : ℂ)) *
      Complex.exp (Complex.I * ((Real.pi / (b - a) : ℝ) : ℂ) * (b : ℂ)) = -1 := by
    rw [← Complex.exp_add]
    have : -Complex.I * ((Real.pi / (b - a) : ℝ) : ℂ) * (a : ℂ) +
        Complex.I * ((Real.pi / (b - a) : ℝ) : ℂ) * (b : ℂ) = Real.pi * Complex.I := by
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_pi_mul_I]
  rw [heq, ← Complex.exp_add] at h1
  have : -Complex.I * ((Real.pi / (b - a) : ℝ) : ℂ) * (b : ℂ) +
      Complex.I * ((Real.pi / (b - a) : ℝ) : ℂ) * (b : ℂ) = 0 := by ring
  rw [this, Complex.exp_zero] at h1
  norm_num at h1

lemma X7_timeEv_fromChoi {d : ℕ} (E : Fin d → ℝ) (t : ℝ)
    (J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (X : Mat d) (x y : Fin d) :
    fromChoi J (timeEvolution E t X) x y =
      ∑ u, ∑ v, J (x,u) (y,v) * (Complex.exp (-Complex.I * (t : ℂ) * ((E u - E v : ℝ) : ℂ)) * X u v) := by
  rfl

lemma X7_cov_iff {d : ℕ} (E : Fin d → ℝ) (J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    IsCovariant E (fromChoi J) ↔
      ∀ x u y v, E x - E u ≠ E y - E v → J (x,u) (y,v) = 0 := by
  constructor
  · intro h x u y v hne
    by_contra hJ
    have hne' : E u - E v ≠ E x - E y := by intro h'; apply hne; linarith
    obtain ⟨t, ht⟩ := X7_exp_ne hne'
    have := congrFun (congrFun (h t (matrixUnit u v)) x) y
    rw [X7_timeEv_fromChoi] at this
    simp only [timeEvolution, fromChoi, matrixUnit, Matrix.single_apply] at this
    rw [Finset.sum_eq_single u, Finset.sum_eq_single v] at this
    · simp only [and_self, if_true, mul_one] at this
      rw [Finset.sum_eq_single u, Finset.sum_eq_single v] at this
      · simp only [and_self, if_true, mul_one] at this
        apply ht
        apply mul_left_cancel₀ hJ
        rw [this, mul_comm]
      · intro w _ hw; simp [Ne.symm hw]
      · simp
      · intro w _ hw; apply Finset.sum_eq_zero; intro z _; simp [Ne.symm hw]
      · simp
    · intro w _ hw; simp [Ne.symm hw]
    · simp
    · intro w _ hw; apply Finset.sum_eq_zero; intro z _; simp [Ne.symm hw]
    · simp
  · intro h t X
    ext x y
    rw [X7_timeEv_fromChoi]
    simp only [timeEvolution, fromChoi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases he : E x - E u = E y - E v
    · have : E u - E v = E x - E y := by linarith
      rw [this]; ring
    · rw [h x u y v he]; ring

end

end QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
theorem solution :
    (∀ Phi : Map 4, FixedChannelFeasible Phi ↔
      FixedChoiFeasible (choi Phi) ∧ ∀ X, fromChoi (choi Phi) X = Phi X) ∧
    (∀ J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ,
      FixedChoiFeasible J ↔ FixedChannelFeasible (fromChoi J) ∧ choi (fromChoi J) = J) := by
  have part1 : ∀ Phi : Map 4, FixedChannelFeasible Phi ↔
      FixedChoiFeasible (choi Phi) ∧ ∀ X, fromChoi (choi Phi) X = Phi X := by
    intro Phi
    constructor
    · rintro ⟨⟨⟨m, K, hK, hPhi⟩, hcov, hgibbs⟩, hpop⟩
      have hPhiK : Phi = krausApply K := funext hPhi
      subst hPhiK
      have hJ := X7_choi_kraus K
      have hrec : ∀ X, fromChoi (choi (krausApply K)) X = krausApply K X := X7_fromChoi_kraus hJ
      have hrecF : fromChoi (choi (krausApply K)) = krausApply K := funext hrec
      refine ⟨⟨X7_psd_of_KForm hJ, (X7_TP_iff hJ).mp hK, ?_, ?_, ?_⟩, hrec⟩
      · rw [← hrecF] at hgibbs; exact (X7_gibbs_iff fixedEnergy 1 _).mp hgibbs
      · rw [← hrecF] at hcov; exact (X7_cov_iff fixedEnergy _).mp hcov
      · rw [hrecF]; exact hpop
    · rintro ⟨⟨hpsd, htp, hgib, hsupp, hpop⟩, hrec⟩
      have hrecF : fromChoi (choi Phi) = Phi := funext hrec
      obtain ⟨m, K, hK⟩ := X7_KForm_of_psd hpsd
      refine ⟨⟨⟨m, K, (X7_TP_iff hK).mpr htp, fun ρ => ?_⟩, ?_, ?_⟩, ?_⟩
      · rw [← hrec ρ]; exact X7_fromChoi_kraus hK ρ
      · rw [← hrecF]; exact (X7_cov_iff _ _).mpr hsupp
      · rw [← hrecF]; exact (X7_gibbs_iff _ _ _).mpr hgib
      · rw [← hrecF]; exact hpop
  refine ⟨part1, fun J => ?_⟩
  have h := part1 (fromChoi J)
  rw [X7_choi_fromChoi] at h
  constructor
  · intro hJ; exact ⟨h.mpr ⟨hJ, fun X => rfl⟩, X7_choi_fromChoi J⟩
  · rintro ⟨hF, -⟩; exact (h.mp hF).1

end
