-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.grand_canonical_variational
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:16:12.087152+00:00
-- url     : https://prove2.me/submissions/5118a212-5fcc-4730-b1e3-b93799fe52ac

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_entropy_variational
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_entropy_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_kms_iff_gibbs
noncomputable section
open Filter MeasureTheory
namespace QAlgorithms.Papers.Independent.Next46.P23
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

variable {I : Type} [Fintype I] [DecidableEq I]

section S173Rdiff
open scoped Matrix.Norms.Operator

lemma S173R_diffZ (H N : Mat I) (u v : ℝ × ℝ → ℝ) (x : ℝ × ℝ)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    DifferentiableAt ℝ (fun y => (NormedSpace.exp ((u y) • H) * NormedSpace.exp ((v y) • N)).trace.re) x := by
  haveI : CompleteSpace (Matrix I I ℂ) := FiniteDimensional.complete ℝ _
  have h1 : DifferentiableAt ℝ (fun y => NormedSpace.exp ((u y) • H)) x :=
    (differentiable_exp_smul_const ℝ H).differentiableAt.comp x hu
  have h2 : DifferentiableAt ℝ (fun y => NormedSpace.exp ((v y) • N)) x :=
    (differentiable_exp_smul_const ℝ N).differentiableAt.comp x hv
  let T : Matrix I I ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap I ℝ ℂ))
  exact T.differentiableAt.comp x (h1.mul h2)

end S173Rdiff

open scoped Matrix ComplexOrder

def S173R_A (H N : Mat I) (c d : ℝ) : Mat I := (-(c : ℂ)) • (H - (d : ℂ) • N)

lemma S173R_ev (H N ρ : Mat I) (c d : ℝ) :
    ev ρ (S173R_A H N c d) = -c * (ev ρ H - d * ev ρ N) := by
  simp only [S173R_A, ev, QAlgorithms.effectProb, Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_smul,
    Matrix.trace_sub, smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, Complex.sub_im, Complex.mul_im]
  ring

lemma S173R_herm (H N : Mat I) (hH : H.IsHermitian) (hN : N.IsHermitian) (c d : ℝ) :
    (S173R_A H N c d).IsHermitian := by
  unfold S173R_A Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH.eq, hN.eq]
  simp [Complex.star_def]

lemma S173R_split (H N : Mat I) (hcomm : H * N = N * H) (c d : ℝ) :
    NormedSpace.exp (S173R_A H N c d) = NormedSpace.exp ((-c) • H) * NormedSpace.exp ((c * d) • N) := by
  have e : S173R_A H N c d = (-c) • H + (c * d) • N := by
    unfold S173R_A
    rw [smul_sub, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul]
    push_cast; rw [sub_eq_add_neg, ← neg_smul]; congr 2; ring
  rw [e, Matrix.exp_add_of_commute]
  exact (Commute.smul_right (hcomm : Commute H N) (c * d)).smul_left (-c)

lemma S173R_Zne [Nonempty I] (A : Mat I) (hA : A.IsHermitian) : (NormedSpace.exp A).trace.re ≠ 0 := by
  have hd := (entropy_variational.2 A hA).1
  have htr := hd.2
  unfold QAlgorithms.gibbsState at htr
  rw [Matrix.trace_smul, smul_eq_mul] at htr
  have hne : (NormedSpace.exp A).trace ≠ 0 := by intro h; rw [h] at htr; simp at htr
  have hh : (NormedSpace.exp A).IsHermitian := hA.exp
  have him : (NormedSpace.exp A).trace.im = 0 := by
    have := Matrix.trace_conjTranspose (NormedSpace.exp A)
    rw [hh.eq] at this
    exact (Complex.conj_eq_iff_im.mp this.symm)
  intro hre; apply hne; exact Complex.ext hre him

theorem S173R_main [Nonempty I] (H N : Mat I) (hH : H.IsHermitian)
    (hN : N.IsHermitian) (hcomm : H*N = N*H) (beta mu : ℝ) :
    let rhoG := QAlgorithms.gibbsState ((-(beta : ℂ)) • (H - (mu : ℂ) • N))
    entropy rhoG = beta * (ev rhoG H - mu * ev rhoG N) +
      Real.log ((NormedSpace.exp ((-(beta : ℂ)) • (H - (mu : ℂ) • N))).trace.re) ∧
    QAlgorithms.IsDensityMatrix rhoG ∧
    (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
      ev rho H = ev rhoG H → ev rho N = ev rhoG N →
        entropy rho ≤ entropy rhoG ∧ (entropy rho = entropy rhoG ↔ rho = rhoG)) ∧
    (∀ A B : Mat I, A*N = N*A → B*N = N*B →
      (rhoG * (complexTau H (-Complex.I * (beta : ℂ)) B * A)).trace = (rhoG * (A*B)).trace) ∧
    (∀ b m : ℝ × ℝ → ℝ, ∀ x : ℝ × ℝ,
      DifferentiableAt ℝ b x → DifferentiableAt ℝ m x →
      (∀ᶠ y in nhds x,
        let rhoY := QAlgorithms.gibbsState ((-(b y : ℂ)) • (H - (m y : ℂ) • N))
        ev rhoY H = y.1 ∧ ev rhoY N = y.2) →
      let S : ℝ × ℝ → ℝ := fun y => entropy
        (QAlgorithms.gibbsState ((-(b y : ℂ)) • (H - (m y : ℂ) • N)))
      fderiv ℝ S x (1,0) = b x ∧ fderiv ℝ S x (0,1) = -b x * m x) := by
  intro rhoG
  have hrG : rhoG = QAlgorithms.gibbsState (S173R_A H N beta mu) := rfl
  clear_value rhoG
  subst hrG
  have hA0 := S173R_herm H N hH hN beta mu
  have hfold : ∀ c d : ℝ, (-(c : ℂ)) • (H - (d : ℂ) • N) = S173R_A H N c d := fun _ _ => rfl
  simp only [hfold]
  obtain ⟨hGd, hG2⟩ := entropy_variational.2 _ hA0
  have hent := (entropy_properties (I := I)).2.2.2.1 _ hA0
  refine ⟨?_, hGd, ?_, ?_, ?_⟩
  · show entropy (QAlgorithms.gibbsState (S173R_A H N beta mu)) = _
    rw [hent, S173R_ev]; ring
  · intro rho hrho h1 h2
    have hle := (hG2 rho hrho).1
    have hiff := (hG2 rho hrho).2
    have heqG := (hG2 _ hGd).2.mpr rfl
    have e1 : ev rho (S173R_A H N beta mu) = ev (QAlgorithms.gibbsState (S173R_A H N beta mu)) (S173R_A H N beta mu) := by
      rw [S173R_ev, S173R_ev, h1, h2]
    refine ⟨by linarith, ⟨fun h => hiff.mp (by linarith), fun h => by rw [h]⟩⟩
  · intro A B _ hB
    have hHN : (H - (mu : ℂ) • N).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH.eq, hN.eq]; simp [Complex.star_def]
    have hk := (kms_iff_gibbs (H - (mu : ℂ) • N) _ hHN hGd beta).mpr rfl
    have htau : complexTau (H - (mu : ℂ) • N) (-Complex.I * (beta : ℂ)) B =
        complexTau H (-Complex.I * (beta : ℂ)) B := by
      unfold complexTau
      set z := -Complex.I * (beta : ℂ)
      have cHN : ∀ p q : ℂ, Commute (p • H) (q • N) := fun p q =>
        Commute.smul_left (Commute.smul_right hcomm _) _
      have s1 : (Complex.I * z) • (H - (mu : ℂ) • N) = (Complex.I * z) • H + (-(Complex.I * z * mu)) • N := by
        rw [smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul]
      have s2 : (-Complex.I * z) • (H - (mu : ℂ) • N) = (-Complex.I * z) • H + (Complex.I * z * mu) • N := by
        rw [smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul]; congr 2; ring
      rw [s1, s2, Matrix.exp_add_of_commute _ _ (cHN _ _), Matrix.exp_add_of_commute _ _ (cHN _ _)]
      have cB : ∀ q : ℂ, Commute B (NormedSpace.exp (q • N)) := fun q =>
        Commute.exp_right (Commute.smul_right hB q)
      have cH : ∀ p q : ℂ, Commute (NormedSpace.exp (p • H)) (NormedSpace.exp (q • N)) := fun p q =>
        Commute.exp (cHN p q)
      have hinv : NormedSpace.exp ((-(Complex.I * z * mu)) • N) * NormedSpace.exp ((Complex.I * z * mu) • N) = 1 := by
        rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl N).smul_left _ |>.smul_right _), ← add_smul,
          neg_add_cancel, zero_smul, NormedSpace.exp_zero]
      calc NormedSpace.exp ((Complex.I * z) • H) * NormedSpace.exp ((-(Complex.I * z * mu)) • N) * B *
            (NormedSpace.exp ((-Complex.I * z) • H) * NormedSpace.exp ((Complex.I * z * mu) • N))
          = NormedSpace.exp ((Complex.I * z) • H) * B * NormedSpace.exp ((-Complex.I * z) • H) *
            (NormedSpace.exp ((-(Complex.I * z * mu)) • N) * NormedSpace.exp ((Complex.I * z * mu) • N)) := by
            rw [Matrix.mul_assoc (NormedSpace.exp ((Complex.I * z) • H)), (cB _).symm.eq]
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (NormedSpace.exp ((-(Complex.I * z * mu)) • N)) (NormedSpace.exp ((-Complex.I * z) • H)),
              (cH _ _).symm.eq]
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hinv, Matrix.mul_one]
    have := hk A B
    rw [htau] at this
    exact this.symm
  · intro b m x hb hm hev
    try simp only [hfold] at hev
    set S : ℝ × ℝ → ℝ := fun y => entropy (QAlgorithms.gibbsState (S173R_A H N (b y) (m y))) with hS
    set Z : ℝ × ℝ → ℝ := fun y => (NormedSpace.exp (S173R_A H N (b y) (m y))).trace.re with hZ
    have hform : ∀ᶠ y in nhds x, S y = Real.log (Z y) + b y * (y.1 - m y * y.2) := by
      filter_upwards [hev] with y hy
      obtain ⟨h1, h2⟩ := hy
      show entropy (QAlgorithms.gibbsState (S173R_A H N (b y) (m y))) = _
      rw [(entropy_properties (I := I)).2.2.2.1 _ (S173R_herm H N hH hN _ _), S173R_ev, h1, h2]
      ring
    have hZsplit : Z = fun y => (NormedSpace.exp ((-(b y)) • H) * NormedSpace.exp ((b y * m y) • N)).trace.re := by
      funext y; simp only [hZ, S173R_split H N hcomm]
    have hZd : DifferentiableAt ℝ Z x := by
      rw [hZsplit]; exact S173R_diffZ H N _ _ x hb.neg (hb.mul hm)
    have hZne : Z x ≠ 0 := S173R_Zne _ (S173R_herm H N hH hN _ _)
    have hFd : DifferentiableAt ℝ (fun y => Real.log (Z y) + b y * (y.1 - m y * y.2)) x := by
      refine (hZd.log hZne).add (hb.mul (differentiableAt_fst.sub (hm.mul differentiableAt_snd)))
    have hSd : DifferentiableAt ℝ S x := hFd.congr_of_eventuallyEq hform
    set ℓ : ℝ × ℝ →L[ℝ] ℝ := b x • ContinuousLinearMap.fst ℝ ℝ ℝ - (b x * m x) • ContinuousLinearMap.snd ℝ ℝ ℝ
    set L : ℝ × ℝ → ℝ := fun y => Real.log (Z x) + ℓ y
    have hLd : HasFDerivAt L ℓ x := ℓ.hasFDerivAt.const_add _
    have hle : ∀ᶠ y in nhds x, S y ≤ L y := by
      filter_upwards [hev] with y hy
      obtain ⟨h1, h2⟩ := hy
      have hdy := (entropy_variational.2 _ (S173R_herm H N hH hN (b y) (m y))).1
      have := ((entropy_variational.2 _ (S173R_herm H N hH hN (b x) (m x))).2 _ hdy).1
      rw [S173R_ev, h1, h2] at this
      show entropy (QAlgorithms.gibbsState (S173R_A H N (b y) (m y))) ≤ _
      simp only [L, ℓ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
      linarith
    have hx : S x = L x := by
      rw [hform.self_of_nhds]
      simp only [L, ℓ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
      ring
    have hmax : IsLocalMax (fun y => S y - L y) x := by
      filter_upwards [hle] with y hy
      rw [hx, sub_self]; linarith
    have h0 := hmax.fderiv_eq_zero
    rw [fderiv_fun_sub hSd hLd.differentiableAt, hLd.fderiv, sub_eq_zero] at h0
    rw [h0]
    simp only [ℓ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    constructor <;> ring

end QAlgorithms.Papers.Independent.Next46.P23

open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P60 (Mat) in
theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (H N : Mat I) (hH : H.IsHermitian)
    (hN : N.IsHermitian) (hcomm : H*N = N*H) (beta mu : ℝ) :
    let rhoG := QAlgorithms.gibbsState ((-(beta : ℂ)) • (H - (mu : ℂ) • N))
    entropy rhoG = beta * (ev rhoG H - mu * ev rhoG N) +
      Real.log ((NormedSpace.exp ((-(beta : ℂ)) • (H - (mu : ℂ) • N))).trace.re) ∧
    QAlgorithms.IsDensityMatrix rhoG ∧
    (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
      ev rho H = ev rhoG H → ev rho N = ev rhoG N →
        entropy rho ≤ entropy rhoG ∧ (entropy rho = entropy rhoG ↔ rho = rhoG)) ∧
    (∀ A B : Mat I, A*N = N*A → B*N = N*B →
      (rhoG * (complexTau H (-Complex.I * (beta : ℂ)) B * A)).trace = (rhoG * (A*B)).trace) ∧
    (∀ b m : ℝ × ℝ → ℝ, ∀ x : ℝ × ℝ,
      DifferentiableAt ℝ b x → DifferentiableAt ℝ m x →
      (∀ᶠ y in nhds x,
        let rhoY := QAlgorithms.gibbsState ((-(b y : ℂ)) • (H - (m y : ℂ) • N))
        ev rhoY H = y.1 ∧ ev rhoY N = y.2) →
      let S : ℝ × ℝ → ℝ := fun y => entropy
        (QAlgorithms.gibbsState ((-(b y : ℂ)) • (H - (m y : ℂ) • N)))
      fderiv ℝ S x (1,0) = b x ∧ fderiv ℝ S x (0,1) = -b x * m x) :=
  S173R_main H N hH hN hcomm beta mu
