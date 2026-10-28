-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.pseudoDiagonalAndEB
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:52:14.659269+00:00
-- url     : https://prove2.me/submissions/fb607431-c9c0-4c29-8c94-f091ccc6443b

import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_kraus_complement
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Gap20 QAlgorithms.Papers.Independent.Gap20.P19
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker
open Filter Topology
open QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Claimed50.P48
open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)
open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)
open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)
open QAlgorithms.Papers.Independent.Information100.P69 (choi)
open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B C E F R K A2 B2 E2 : Type}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [Fintype E] [DecidableEq E] [Nonempty E]
variable [Fintype F] [DecidableEq F] [Nonempty F]
variable [Fintype R] [DecidableEq R] [Nonempty R]
variable [Fintype K] [DecidableEq K]
variable [Fintype A2] [DecidableEq A2] [Nonempty A2]
variable [Fintype B2] [DecidableEq B2] [Nonempty B2]
variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

theorem S174B_chan {K' ι κ : Type} [Fintype K'] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K' → Matrix κ ι ℂ) (h : ∑ j, (E j)ᴴ * E j = 1) : IsChannel (krausApply E) := by
  refine ⟨Fintype.card K', fun j => E ((Fintype.equivFin K').symm j), ?_, fun rho => ?_⟩
  · unfold IsKrausFamily
    rw [← h]; exact Equiv.sum_comp (Fintype.equivFin K').symm (fun j => (E j)ᴴ * E j)
  · unfold krausApply
    exact (Equiv.sum_comp (Fintype.equivFin K').symm (fun j => E j * rho * (E j)ᴴ)).symm

theorem S174B_kapp {K' ι κ : Type} [Fintype K'] [Fintype ι] (E : K' → Matrix κ ι ℂ)
    (X : Matrix ι ι ℂ) (y y' : κ) :
    krausApply E X y y' = ∑ k, ∑ x, ∑ x', E k y x * X x x' * star (E k y' x') := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]

theorem S174B_single {K' ι κ : Type} [Fintype K'] [Fintype ι] [DecidableEq ι]
    (E : K' → Matrix κ ι ℂ) (x x' : ι) (y y' : κ) :
    krausApply E (Matrix.single x x' 1) y y' = ∑ k, E k y x * star (E k y' x') := by
  rw [S174B_kapp]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem S174B_lin {K' ι κ : Type} [Fintype K'] [Fintype ι] [DecidableEq ι]
    (E : K' → Matrix κ ι ℂ) (X : Matrix ι ι ℂ) (y y' : κ) :
    krausApply E X y y' = ∑ x, ∑ x', X x x' * krausApply E (Matrix.single x x' 1) y y' := by
  simp only [S174B_single]
  simp only [S174B_kapp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem S174B_ext {K1 K2 ι κ : Type} [Fintype K1] [Fintype K2] [Fintype ι] [DecidableEq ι]
    (E : K1 → Matrix κ ι ℂ) (E' : K2 → Matrix κ ι ℂ)
    (h : ∀ x x' y y', ∑ k, E k y x * star (E k y' x') = ∑ k, E' k y x * star (E' k y' x')) :
    krausApply E = krausApply E' := by
  funext X; ext y y'
  rw [S174B_lin, S174B_lin E']
  simp only [S174B_single, h]

theorem S174B_smul {K' ι κ : Type} [Fintype K'] [Fintype ι]
    (E : K' → Matrix κ ι ℂ) (c : ℂ) (X : Matrix ι ι ℂ) :
    krausApply E (c • X) = c • krausApply E X := by
  simp [krausApply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

theorem S174B_TP {K1 K2 ι κ : Type} [Fintype K1] [Fintype K2] [Fintype ι] [DecidableEq ι]
    [Fintype κ] (E0 : K1 → Matrix κ ι ℂ) (h0 : IsKrausFamily E0) (E : K2 → Matrix κ ι ℂ)
    (h : ∀ ρ, krausApply E0 ρ = krausApply E ρ) : IsKrausFamily E := by
  have tr : ∀ {K3 : Type} [Fintype K3] (F : K3 → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ),
      (krausApply F ρ).trace = ((∑ j, (F j)ᴴ * F j) * ρ).trace := by
    intro K3 _ F ρ
    simp only [krausApply, Matrix.trace_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  unfold IsKrausFamily at *
  ext x x'
  have := tr E (Matrix.single x' x 1)
  rw [← h, tr E0, h0, Matrix.trace_mul_single, Matrix.trace_mul_single] at this
  simp at this
  exact this.symm

theorem S174B_iso {K' : Type} [Fintype K'] (E : K' → Matrix B A ℂ) (h : IsKrausFamily E) :
    IsIsometry (indexedKrausDilation E) := by
  unfold IsIsometry
  unfold IsKrausFamily at h
  rw [← h]
  ext a a'
  simp only [Matrix.mul_apply, indexedKrausDilation, Matrix.sum_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

theorem S174B_norm {Y : Type} [Fintype Y] [Nonempty Y] (x : Y → ℂ) :
    ∃ u : Y → ℂ, ∑ y, star (u y) * u y = 1 ∧
      Matrix.vecMulVec x (star x) = (∑ y, star (x y) * x y) • Matrix.vecMulVec u (star u) := by
  have hS : (∑ y, star (x y) * x y) = (((∑ y, Complex.normSq (x y) : ℝ)) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  by_cases hx : x = 0
  · refine ⟨Pi.single (Classical.arbitrary Y) 1, ?_, ?_⟩
    · simp [Pi.single_apply]
    · subst hx; simp
  · set s : ℝ := ∑ y, Complex.normSq (x y) with hs
    have hpos : 0 < s := by
      obtain ⟨y0, hy0⟩ : ∃ y, x y ≠ 0 := by
        by_contra hc; push_neg at hc; exact hx (funext hc)
      have : 0 < Complex.normSq (x y0) := Complex.normSq_pos.mpr hy0
      calc 0 < Complex.normSq (x y0) := this
        _ ≤ s := Finset.single_le_sum (f := fun y => Complex.normSq (x y))
              (fun y _ => Complex.normSq_nonneg _) (Finset.mem_univ y0)
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hpos.le
    have hsq0 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    refine ⟨fun y => ((Real.sqrt s : ℂ))⁻¹ * x y, ?_, ?_⟩
    · have : ∀ y, star (((Real.sqrt s : ℂ))⁻¹ * x y) * (((Real.sqrt s : ℂ))⁻¹ * x y)
          = ((s : ℂ))⁻¹ * (star (x y) * x y) := by
        intro y
        have h1 : star (((Real.sqrt s : ℂ))⁻¹) = ((Real.sqrt s : ℂ))⁻¹ := by
          simp [Complex.conj_ofReal]
        rw [star_mul', h1]
        have h2 : ((s : ℂ)) = ((Real.sqrt s : ℂ)) ^ 2 := by exact_mod_cast hsq.symm
        rw [h2]
        have : ((Real.sqrt s : ℂ)) ≠ 0 := by exact_mod_cast hsq0
        field_simp
      simp only [this, ← Finset.mul_sum, hS]
      have : ((s : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp
    · rw [hS]
      ext i j
      simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.star_apply, smul_eq_mul, star_mul']
      have h1 : star (((Real.sqrt s : ℂ))⁻¹) = ((Real.sqrt s : ℂ))⁻¹ := by
        simp [Complex.conj_ofReal]
      rw [h1]
      have h2 : ((s : ℂ)) = ((Real.sqrt s : ℂ)) ^ 2 := by exact_mod_cast hsq.symm
      rw [h2]
      have : ((Real.sqrt s : ℂ)) ≠ 0 := by exact_mod_cast hsq0
      field_simp

theorem S174B_Dchan {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] (U : Matrix X X ℂ)
    (hU : U * Uᴴ = 1) (u : X → Y → ℂ) (hu : ∀ k, ∑ y, star (u k y) * u k y = 1) :
    IsChannel (fun σ : Matrix X X ℂ =>
      ∑ k, (Uᴴ * σ * U) k k • Matrix.vecMulVec (u k) (star (u k))) := by
  let F : X → Matrix Y X ℂ := fun k => Matrix.of fun y x => u k y * star (U x k)
  have hF : (fun σ : Matrix X X ℂ =>
      ∑ k, (Uᴴ * σ * U) k k • Matrix.vecMulVec (u k) (star (u k))) = krausApply F := by
    funext σ; ext y y'
    rw [S174B_kapp]
    simp only [F, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul, Pi.star_apply, Finset.sum_mul,
      star_mul', star_star]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    ring
  rw [hF]
  apply S174B_chan
  rw [← hU]
  ext x x'
  simp only [F, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_mul', star_star]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have := hu k
  calc ∑ y, star (u k y) * U x k * (u k y * star (U x' k))
      = (∑ y, star (u k y) * u k y) * (U x k * star (U x' k)) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun y _ => ?_); ring
    _ = U x k * star (U x' k) := by rw [this, one_mul]

theorem S174B_G0 {n : ℕ} (f : Fin n → B → ℂ) (g : Fin n → A → ℂ)
    (hK : IsKrausFamily (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))) :
    ∃ W : Matrix (B × Fin n) A ℂ,
      receiverChannel W = krausApply (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))
        ∧ IsAntidegradable W := by
  set E : Fin n → Matrix B A ℂ := fun k => Matrix.of fun y x => f k y * g k x with hEdef
  have hKC := kraus_complement E
  choose u hu1 hu2 using fun k => S174B_norm (f k)
  refine ⟨indexedKrausDilation E, hKC.1, S174B_iso E hK, ?_⟩
  have hD := S174B_Dchan (1 : Matrix (Fin n) (Fin n) ℂ) (by simp) u hu1
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hD
  refine ⟨fun σ : Matrix (Fin n) (Fin n) ℂ => ∑ k, σ k k •
      Matrix.vecMulVec (u k) (star (u k)), hD, fun ρ => ?_⟩
  rw [hKC.1]
  have hk : ∀ k, E k * ρ * (E k)ᴴ = (∑ x, ∑ x', g k x * ρ x x' * star (g k x')) •
      Matrix.vecMulVec (f k) (star (f k)) := by
    intro k; ext y y'
    simp only [E, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, Pi.star_apply, star_mul', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    ring
  have hc : ∀ k, complementaryChannel (indexedKrausDilation E) ρ k k =
      (∑ x, ∑ x', g k x * ρ x x' * star (g k x')) * ∑ y, star (f k y) * f k y := by
    intro k
    rw [(hKC.2.1 ρ k k).1, hk, Matrix.trace_smul, Matrix.trace_vecMulVec]
    simp [dotProduct, mul_comm]
  simp only [hc]
  unfold krausApply
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hk, hu2 k, smul_smul]

theorem S174B_G {K' : Type} [Fintype K'] (f : K' → B → ℂ) (g : K' → A → ℂ)
    (hK : IsKrausFamily (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))) :
    ∃ n : ℕ, ∃ W : Matrix (B × Fin n) A ℂ,
      receiverChannel W = krausApply (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))
        ∧ IsAntidegradable W := by
  let e := (Fintype.equivFin K').symm
  have hK' : IsKrausFamily (fun k => (Matrix.of fun y x => f (e k) y * g (e k) x : Matrix B A ℂ)) := by
    unfold IsKrausFamily at *
    rw [← hK]
    exact Equiv.sum_comp e (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ)ᴴ *
      (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ))
  obtain ⟨W, hW1, hW2⟩ := S174B_G0 (fun k => f (e k)) (fun k => g (e k)) hK'
  refine ⟨Fintype.card K', W, ?_, hW2⟩
  rw [hW1]
  funext ρ
  unfold krausApply
  exact Equiv.sum_comp e (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ) * ρ *
      (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ)ᴴ)

theorem S174B_dXd {X : Type} [Fintype X] [DecidableEq X] (d : X → ℂ) (M : Matrix X X ℂ) (a b : X) :
    (Matrix.diagonal d * M * (Matrix.diagonal d)ᴴ) a b = d a * M a b * star (d b) := by
  simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]

theorem S174B_dXd' {X : Type} [Fintype X] [DecidableEq X] (d d' : X → ℂ) (M : Matrix X X ℂ) (a b : X) :
    (Matrix.diagonal d * M * (Matrix.diagonal d')ᴴ) a b = d a * M a b * star (d' b) := by
  simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]

theorem S174B_PD (Phi : Superop A B) (hPhi : IsChannel Phi) (hPD : PseudoDiagonal Phi) :
    ∃ envSize : ℕ, ∃ witness : Matrix (B × Fin envSize) A ℂ,
      receiverChannel witness = Phi ∧ IsDegradable witness := by
  obtain ⟨m0, E0, hE0K, hE0⟩ := hPhi
  obtain ⟨c, hc, w, V, hV⟩ := hPD
  obtain ⟨m, v, hcv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hc
  have hVV : (V : Matrix B B ℂ)ᴴ * (V : Matrix B B ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp V.2
  have hVV' : (V : Matrix B B ℂ) * (V : Matrix B B ℂ)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp V.2
  set Wb : Matrix B A ℂ := Matrix.of fun a i => star (w a i) with hWb
  set G : Fin m → Matrix B A ℂ := fun t => (V : Matrix B B ℂ) * Matrix.diagonal (v t) * Wb with hG
  have hM : ∀ ρ, arbitraryVectorComplement c w ρ =
      ∑ t, Matrix.diagonal (v t) * (Wb * ρ * Wbᴴ) * (Matrix.diagonal (v t))ᴴ := by
    intro ρ; ext a b
    rw [Matrix.sum_apply]
    simp only [S174B_dXd]
    simp only [arbitraryVectorComplement, hcv, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, hWb, Matrix.of_apply, star_star,
      Pi.star_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.sum_comm]
    simp only [starRingEnd_apply]
    ring
  have hPhiG : ∀ ρ, Phi ρ = krausApply G ρ := by
    intro ρ
    rw [hV, conjSuperop, hM]
    simp only [krausApply, G, Matrix.conjTranspose_mul, Finset.mul_sum, Finset.sum_mul,
      Matrix.mul_assoc]
  have hGK : IsKrausFamily G := S174B_TP E0 hE0K G (fun ρ => by rw [← hE0, hPhiG])
  have hKC := kraus_complement G
  have : Nonempty (Fin m) := by
    rcases m with _ | m
    · exfalso
      have h1 := congrFun (congrFun hGK (Classical.arbitrary A)) (Classical.arbitrary A)
      simp at h1
    · exact ⟨0⟩
  choose u hu1 hu2 using fun a => S174B_norm (fun t => v t a)
  refine ⟨m, indexedKrausDilation G, ?_, ?_, ?_⟩
  · rw [hKC.1]; funext ρ; exact (hPhiG ρ).symm
  · exact S174B_iso G hGK
  refine ⟨fun σ => ∑ a, ((V : Matrix B B ℂ)ᴴ * σ * V) a a • Matrix.vecMulVec (u a) (star (u a)),
    ?_, fun ρ => ?_⟩
  · convert S174B_Dchan V hVV' u hu1
  rw [hKC.1, ← hPhiG, hV]
  have hVMV : ∀ M : Matrix B B ℂ, (V : Matrix B B ℂ)ᴴ * conjSuperop (V : Matrix B B ℂ) M * V = M := by
    intro M
    simp only [conjSuperop, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
    rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
  simp only [hVMV]
  ext t t'
  rw [(hKC.2.1 ρ t t').1]
  have hGt : G t * ρ * (G t')ᴴ = (V : Matrix B B ℂ) * (Matrix.diagonal (v t) * (Wb * ρ * Wbᴴ) *
      (Matrix.diagonal (v t'))ᴴ) * (V : Matrix B B ℂ)ᴴ := by
    simp only [G, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hGt, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hMa : ∀ a, arbitraryVectorComplement c w ρ a a • Matrix.vecMulVec (u a) (star (u a)) =
      (Wb * ρ * Wbᴴ) a a • Matrix.vecMulVec (fun t => v t a) (star (fun t => v t a)) := by
    intro a
    rw [hu2 a, smul_smul, hM]
    congr 1
    simp only [Matrix.sum_apply, S174B_dXd]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    ring
  simp only [hMa, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Pi.star_apply, Matrix.trace, Matrix.diag_apply, S174B_dXd']
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

theorem S174B_EB (Phi : Superop A B) (hPhi : IsChannel Phi) (hEB : ChannelEB Phi) :
    ∃ envSize : ℕ, ∃ witness : Matrix (B × Fin envSize) A ℂ,
      receiverChannel witness = Phi ∧ IsAntidegradable witness := by
  obtain ⟨m0, E0, hE0K, hE0⟩ := hPhi
  obtain rfl : Phi = krausApply E0 := funext hE0
  unfold ChannelEB QAlgorithms.Papers.Independent.Dependency50.P41.EntanglementBreaking at hEB
  set d := Fintype.card A with hd
  set eA := Fintype.equivFin A
  set eB := Fintype.equivFin B
  have hdpos : (0:ℝ) < d := by exact_mod_cast Fintype.card_pos
  let psi : EuclideanSpace ℂ (Fin d × Fin d) :=
    WithLp.toLp 2 (fun p => if p.1 = p.2 then ((Real.sqrt d : ℂ))⁻¹ else 0)
  have hpsi : ‖psi‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : ∀ p : Fin d × Fin d, ‖psi p‖ ^ 2 = if p.1 = p.2 then (d:ℝ)⁻¹ else 0 := by
      intro p
      simp only [psi]
      split_ifs
      · simp [norm_inv, Real.sq_sqrt hdpos.le]
      · simp
    simp only [this, Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_inv_cancel₀ hdpos.ne', Real.sqrt_one]
  obtain ⟨q, w, AA, BB, hw0, hw1, hden, hX⟩ := hEB psi hpsi
  have key : ∀ x x' y y', krausApply E0 (Matrix.single x x' 1) y y' =
      (d:ℂ) * ∑ j, (w j : ℂ) * (AA j (eA x) (eA x') * BB j (eB y) (eB y')) := by
    intro x x' y y'
    have h1 := congrFun (congrFun hX (eA x, eB y)) (eA x', eB y')
    simp only [idTensorSuperop, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul, Equiv.symm_apply_apply] at h1
    have hmat : (fun a b => pureDensity psi (eA x, eA a) (eA x', eA b)) =
        ((d:ℂ)⁻¹) • (Matrix.single x x' 1 : Matrix A A ℂ) := by
      funext a b
      simp only [pureDensity, psi, Matrix.of_apply, Matrix.smul_apply, Matrix.single_apply,
        EmbeddingLike.apply_eq_iff_eq, smul_eq_mul]
      split_ifs with h2 h3 h4 <;> simp_all
      · rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
        push_cast; rfl
    rw [hmat, S174B_smul, Matrix.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    have : (d:ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    field_simp
  choose mA vA hvA using fun j => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hden j).1.1
  choose mB vB hvB using fun j => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hden j).2.1
  let f : (Σ j : Fin q, Fin (mA j) × Fin (mB j)) → B → ℂ :=
    fun k y => ((Real.sqrt ((d:ℝ) * w k.1) : ℝ) : ℂ) * vB k.1 k.2.2 (eB y)
  let g : (Σ j : Fin q, Fin (mA j) × Fin (mB j)) → A → ℂ := fun k x => vA k.1 k.2.1 (eA x)
  have hEq : krausApply E0 =
      krausApply (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ)) := by
    apply S174B_ext
    intro x x' y y'
    rw [← S174B_single, key]
    simp only [Matrix.of_apply, f, g, Fintype.sum_sigma, Fintype.sum_prod_type, hvA, hvB,
      Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_mul']
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hsq : ((Real.sqrt ((d:ℝ) * w j) : ℝ) : ℂ) * star ((Real.sqrt ((d:ℝ) * w j) : ℝ) : ℂ)
        = (d:ℂ) * (w j : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (mul_nonneg (Nat.cast_nonneg _) (hw0 j))]
      push_cast; rfl
    rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t' _ => ?_)
    linear_combination (-((vA j t (eA x) * star (vA j t (eA x'))) *
      (vB j t' (eB y) * star (vB j t' (eB y'))))) * hsq
  have hK : IsKrausFamily (fun k => (Matrix.of fun y x => f k y * g k x : Matrix B A ℂ)) :=
    S174B_TP E0 hE0K _ (fun ρ => by rw [hEq])
  obtain ⟨n, W, hW1, hW2⟩ := S174B_G f g hK
  exact ⟨n, W, hW1.trans hEq.symm, hW2⟩

theorem solution [Nonempty A] [Nonempty B] :
    (∀ Phi : Superop A B, IsChannel Phi → PseudoDiagonal Phi → (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsDegradable witness)) ∧
    (∀ Phi : Superop A B, IsChannel Phi → ChannelEB Phi → (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness)) := by
  exact ⟨S174B_PD, S174B_EB⟩

end
