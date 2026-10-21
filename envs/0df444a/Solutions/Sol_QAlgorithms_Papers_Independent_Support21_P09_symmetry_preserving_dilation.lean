-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P09.symmetry_preserving_dilation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:52:49.381014+00:00
-- url     : https://prove2.me/submissions/e2a5316f-a5ab-4d40-8ac2-b496c62dfd17

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
noncomputable section
open QAlgorithms.Papers.Independent.Support21.P09
open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix


theorem g66f_conj_pure {I : Type*} [Fintype I] (A : Matrix I I ℂ) (w : I → ℂ) :
    A * Matrix.vecMulVec w (star w) * A.conjTranspose =
      Matrix.vecMulVec (A *ᵥ w) (star (A *ᵥ w)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem g66f_eff_eq {I O : Type*} [Fintype I] (M : Matrix I O ℂ) (o : O) :
    columnEffect M o = Matrix.vecMulVec (fun i => M i o) (star (fun i => M i o)) := by
  ext a b; rfl

theorem g66f_phase {I : Type*} [Fintype I] (w u : I → ℂ) (hu : u ≠ 0)
    (h : Matrix.vecMulVec w (star w) = Matrix.vecMulVec u (star u)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ w = z • u := by
  obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
    by_contra hc; push Not at hc; exact hu (funext hc)
  have hkk := congrFun (congrFun h k) k
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def] at hkk
  rw [Complex.mul_conj, Complex.mul_conj] at hkk
  have hn : Complex.normSq (w k) = Complex.normSq (u k) := by exact_mod_cast hkk
  have hwk : w k ≠ 0 := by
    intro h0; rw [h0, map_zero] at hn; exact hk (Complex.normSq_eq_zero.mp hn.symm)
  refine ⟨conj (u k) / conj (w k), ?_, ?_⟩
  · rw [norm_div, Complex.norm_conj, Complex.norm_conj]
    have : ‖w k‖ = ‖u k‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (w k)), ← Real.sqrt_sq (norm_nonneg (u k)),
        ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hn]
    rw [this, div_self (norm_ne_zero_iff.mpr hk)]
  · funext i
    have hik := congrFun (congrFun h i) k
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def] at hik
    have hc : conj (w k) ≠ 0 := (map_ne_zero _).mpr hwk
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination hik

theorem g66f_covrep
    {G : Type*} [Group G] [Fintype G] {d n : ℕ} (hd : 0 < d)
    (phi : Rep G (Fin d)) (hphi : UnitaryRep phi)
    (M : Matrix (Fin d) (Fin n) ℂ) (hM : RankOnePOVM M)
    (hdist : Function.Injective (columnEffect M)) (hcov : EffectsCovariant phi M) :
    ∃ R : Rep G (Fin n), ∃ pi : G →* Equiv.Perm (Fin n), ∃ z : G → Fin n → ℂ,
      UnitaryRep R ∧ (∀ g j, ‖z g j‖ = 1) ∧
      (∀ g i j, R g i j = if i = pi g j then z g j else 0) ∧
      (∀ g j i, (phi g).mulVec (fun r => M r j) i = z g j * M i (pi g j)) ∧
      MatrixIntertwines phi R M := by
  classical
  have hm0 : ∀ j, (fun i => M i j) ≠ 0 := hM.1
  choose σ hσ using hcov
  have hconj : ∀ g h (X : Matrix (Fin d) (Fin d) ℂ), phi (g * h) * X * (phi (g * h))ᴴ =
      phi g * (phi h * X * (phi h)ᴴ) * (phi g)ᴴ := by
    intro g h X
    rw [map_mul, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hσmul : ∀ g h o, σ (g * h) o = σ g (σ h o) := by
    intro g h o; apply hdist; rw [← hσ, ← hσ, ← hσ, hconj]
  have hσone : ∀ o, σ 1 o = o := by
    intro o; apply hdist; rw [← hσ, map_one]; simp
  let pi : G →* Equiv.Perm (Fin n) :=
    { toFun := fun g =>
        { toFun := σ g, invFun := σ g⁻¹,
          left_inv := fun o => by rw [← hσmul, inv_mul_cancel, hσone],
          right_inv := fun o => by rw [← hσmul, mul_inv_cancel, hσone] }
      map_one' := by ext o; simp [hσone]
      map_mul' := by intro g h; ext o; simp [hσmul, Equiv.Perm.mul_apply] }
  have hpi : ∀ g o, pi g o = σ g o := fun _ _ => rfl
  have hph : ∀ g j, ∃ c : ℂ, ‖c‖ = 1 ∧
      phi g *ᵥ (fun i => M i j) = c • (fun i => M i (σ g j)) := by
    intro g j
    apply g66f_phase _ _ (hm0 (σ g j))
    have := hσ g j
    rw [g66f_eff_eq, g66f_eff_eq, g66f_conj_pure] at this
    exact this
  choose z hz1 hz using hph
  have hcancel : ∀ (a b : ℂ) j, a • (fun i => M i j) = b • (fun i => M i j) → a = b := by
    intro a b j h
    have h2 : (a - b) • (fun i => M i j) = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (hm0 j)
  have hzmul : ∀ g h j, z (g * h) j = z g (σ h j) * z h j := by
    intro g h j
    apply hcancel _ _ (σ g (σ h j))
    rw [← hσmul, ← hz, map_mul, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_smul, hz, smul_smul,
      hσmul, mul_comm]
  have hzone : ∀ j, z 1 j = 1 := by
    intro j
    apply hcancel _ _ j
    have := hz 1 j
    rw [map_one, Matrix.one_mulVec, hσone] at this
    rw [← this, one_smul]
  let R : Rep G (Fin n) :=
    { toFun := fun g => Matrix.of fun i j => if i = σ g j then z g j else 0
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, hσone, hzone, Matrix.one_apply]
      map_mul' := by
        intro g h
        ext i j
        simp only [Matrix.of_apply, Matrix.mul_apply, mul_ite, mul_zero, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true, hσmul, hzmul] }
  refine ⟨R, pi, z, ?_, hz1, fun g i j => rfl, ?_, ?_⟩
  · intro g
    rw [Matrix.mem_unitaryGroup_iff']
    ext j j'
    simp only [R, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_apply, Matrix.star_apply,
      Matrix.of_apply, Matrix.one_apply]
    simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    by_cases hj : j = j'
    · subst hj
      simp only [if_true]
      rw [RCLike.star_def, Complex.conj_mul', hz1]; simp
    · have : σ g j ≠ σ g j' := fun h => hj ((pi g).injective h)
      rw [if_neg (Ne.symm this), if_neg hj]
  · intro g j i
    have := congrFun (hz g j) i
    rw [this, hpi]; simp
  · intro g
    ext i j
    have h1 := congrFun (hz g j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    simp only [R, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, mul_ite,
      mul_zero]
    rw [h1, Finset.sum_ite_eq']
    simp [mul_comm]


theorem g66f_complete {d c : ℕ} (M : Matrix (Fin d) (Fin (d + c)) ℂ)
    (hMM : M * M.conjTranspose = 1) :
    ∃ B : Matrix (Fin (d + c)) (Fin (d + c)) ℂ, B ∈ Matrix.unitaryGroup (Fin (d + c)) ℂ ∧
      ∀ i j, B (Fin.castAdd c i) j = M i j := by
  classical
  let v : Fin (d + c) → EuclideanSpace ℂ (Fin (d + c)) := fun i =>
    WithLp.toLp 2 (fun j => if h : i.val < d then M ⟨i.val, h⟩ j else 0)
  let s : Set (Fin (d + c)) := Set.range (Fin.castAdd c)
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨x, i, rfl⟩ ⟨y, k, rfl⟩
    have := congrFun (congrFun hMM k) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
    simp only [Set.domRestrict_apply, v, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.coe_castAdd,
      i.isLt, k.isLt, dif_pos, Pi.star_apply, Subtype.mk.injEq]
    simp only [Fin.eta, RCLike.star_def]
    convert this using 1
    · rfl
    by_cases h : k = i
    · subst h; simp
    · rw [if_neg h, if_neg]; intro h'
      exact h (Fin.castAdd_injective _ _ (congrArg Subtype.val h')).symm
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨Matrix.of fun i j => b i j, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i k
    have := orthonormal_iff_ite.mp b.orthonormal k i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [dotProduct, Pi.star_apply] at this
    rw [this]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro i j
    simp only [Matrix.of_apply]
    rw [hb _ ⟨i, rfl⟩]
    simp [v]

theorem g66f_sb_mul {d c : ℕ} (A A' : Matrix (Fin d) (Fin d) ℂ) (B B' : Matrix (Fin c) (Fin c) ℂ) :
    sumBlock A B * sumBlock A' B' = sumBlock (A * A') (B * B') := by
  unfold sumBlock
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp

theorem g66f_sb_one {d c : ℕ} :
    sumBlock (1 : Matrix (Fin d) (Fin d) ℂ) (1 : Matrix (Fin c) (Fin c) ℂ) = 1 := by
  unfold sumBlock; rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem g66f_sb_star {d c : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin c) (Fin c) ℂ) :
    (sumBlock A B).conjTranspose = sumBlock A.conjTranspose B.conjTranspose := by
  unfold sumBlock; rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]; simp

theorem g66f_sb_cc {d c : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin c) (Fin c) ℂ)
    (i k : Fin d) : sumBlock A C (Fin.castAdd c i) (Fin.castAdd c k) = A i k := by
  simp [sumBlock]
theorem g66f_sb_cn {d c : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin c) (Fin c) ℂ)
    (i : Fin d) (k : Fin c) : sumBlock A C (Fin.castAdd c i) (Fin.natAdd d k) = 0 := by
  simp [sumBlock]
theorem g66f_sb_nc {d c : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin c) (Fin c) ℂ)
    (i : Fin c) (k : Fin d) : sumBlock A C (Fin.natAdd d i) (Fin.castAdd c k) = 0 := by
  simp [sumBlock]
theorem g66f_sb_nn {d c : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin c) (Fin c) ℂ)
    (i k : Fin c) : sumBlock A C (Fin.natAdd d i) (Fin.natAdd d k) = C i k := by
  simp [sumBlock]

theorem g66f_sb_ext {d c : ℕ} {A A' : Matrix (Fin d) (Fin d) ℂ} {C C' : Matrix (Fin c) (Fin c) ℂ}
    (h : sumBlock A C = sumBlock A' C') : A = A' ∧ C = C' :=
  ⟨by ext i k; rw [← g66f_sb_cc A C, h, g66f_sb_cc],
   by ext i k; rw [← g66f_sb_nn A C, h, g66f_sb_nn]⟩

/-- the top-row selector -/
def g66f_P (d c : ℕ) : Matrix (Fin d) (Fin (d + c)) ℂ :=
  Matrix.of fun i y => if y = Fin.castAdd c i then 1 else 0

theorem g66f_PB {d c : ℕ} (B : Matrix (Fin (d + c)) (Fin (d + c)) ℂ) (i : Fin d) (x : Fin (d + c)) :
    (g66f_P d c * B) i x = B (Fin.castAdd c i) x := by
  simp [g66f_P, Matrix.mul_apply]

theorem g66f_impl {d c : ℕ} (M : Matrix (Fin d) (Fin (d + c)) ℂ)
    (B : Matrix (Fin (d + c)) (Fin (d + c)) ℂ) (hBu : B ∈ Matrix.unitaryGroup (Fin (d + c)) ℂ)
    (hBtop : ∀ i j, B (Fin.castAdd c i) j = M i j) :
    ImplementsPOVM M B.conjTranspose (Fin.castAdd c) := by
  refine ⟨Unitary.star_mem hBu, ?_⟩
  intro rho _ o
  set ι : Matrix (Fin (d + c)) (Fin d) ℂ := coordinateInclusion (Fin.castAdd c) with hι
  have hPB : (ι.conjTranspose * B : Matrix (Fin d) (Fin (d + c)) ℂ) = M := by
    ext i j
    simp [hι, coordinateInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply, hBtop]
  have hBP : (B.conjTranspose * ι : Matrix (Fin (d + c)) (Fin d) ℂ) = M.conjTranspose := by
    rw [← hPB, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.conjTranspose_conjTranspose]
  have : (B.conjTranspose * (ι * rho * ι.conjTranspose) * B : Matrix (Fin (d + c)) (Fin (d + c)) ℂ)
      = M.conjTranspose * rho * M := by
    rw [← hBP, ← hPB]; simp only [Matrix.mul_assoc]
  rw [this]
  simp only [Matrix.mul_apply, Matrix.trace, Matrix.diag, columnEffect, QAlgorithms.pureDensity,
    Matrix.of_apply, Matrix.conjTranspose_apply, RCLike.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

theorem solution
    {G : Type*} [Group G] [Fintype G] {d c : ℕ} (hd : 0 < d)
    (phi : Rep G (Fin d)) (hphi : UnitaryRep phi)
    (M : Matrix (Fin d) (Fin (d + c)) ℂ) (hM : RankOnePOVM M)
    (hdist : Function.Injective (columnEffect M)) (hcov : EffectsCovariant phi M) :
    ∃ R : Rep G (Fin (d + c)), UnitaryRep R ∧ (∀ g, Monomial (R g)) ∧
    MatrixIntertwines phi R M ∧ ∃ chi : Rep G (Fin c), UnitaryRep chi ∧
    ∃ B : Matrix (Fin (d + c)) (Fin (d + c)) ℂ,
      B ∈ Matrix.unitaryGroup (Fin (d + c)) ℂ ∧
      (∀ i j, B (Fin.castAdd c i) j = M i j) ∧
      (∀ g, sumBlock (phi g) (chi g) * B = B * R g) ∧
      ImplementsPOVM M B.conjTranspose (Fin.castAdd c) := by
  classical
  obtain ⟨R, pi, z, hRu, hz1, hRform, -, hint⟩ := g66f_covrep hd phi hphi M hM hdist hcov
  have hMM : M * M.conjTranspose = 1 := by
    rw [← hM.2.2]
    ext i k
    simp [Matrix.mul_apply, Matrix.sum_apply, columnEffect, QAlgorithms.pureDensity,
      Matrix.conjTranspose_apply]
  obtain ⟨B, hBu, hBtop⟩ := g66f_complete M hMM
  have hBB : B * B.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hBu
  have hBB' : B.conjTranspose * B = 1 := mul_eq_one_comm.mp hBB
  have hRR : ∀ g, R g * (R g).conjTranspose = 1 := fun g => Matrix.mem_unitaryGroup_iff.mp (hRu g)
  have hRinv : ∀ g, (R g).conjTranspose = R g⁻¹ := by
    intro g
    calc (R g).conjTranspose = R (g⁻¹ * g) * (R g).conjTranspose := by simp
      _ = R g⁻¹ := by rw [map_mul, Matrix.mul_assoc, hRR, Matrix.mul_one]
  let T : G → Matrix (Fin (d + c)) (Fin (d + c)) ℂ := fun g => B * R g * B.conjTranspose
  have hTmul : ∀ g h, T (g * h) = T g * T h := by
    intro g h
    show B * R (g * h) * B.conjTranspose = B * R g * B.conjTranspose * (B * R h * B.conjTranspose)
    rw [map_mul]
    calc B * (R g * R h) * B.conjTranspose
        = B * R g * 1 * R h * B.conjTranspose := by simp [Matrix.mul_assoc]
      _ = _ := by rw [← hBB']; simp only [Matrix.mul_assoc]
  have hTstar : ∀ g, (T g).conjTranspose = T g⁻¹ := by
    intro g
    show (B * R g * B.conjTranspose).conjTranspose = B * R g⁻¹ * B.conjTranspose
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hRinv, Matrix.mul_assoc]
  have hPB : g66f_P d c * B = M := by ext i x; rw [g66f_PB, hBtop]
  have hPT : ∀ g, g66f_P d c * T g = phi g * g66f_P d c := by
    intro g
    show g66f_P d c * (B * R g * B.conjTranspose) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPB, ← hint g, hPB.symm, Matrix.mul_assoc,
      Matrix.mul_assoc, hBB, Matrix.mul_one]
  have htop : ∀ g i x, T g (Fin.castAdd c i) x = (phi g * g66f_P d c) i x := by
    intro g i x; rw [← hPT, g66f_PB]
  have hcc : ∀ g i k, T g (Fin.castAdd c i) (Fin.castAdd c k) = phi g i k := by
    intro g i k; rw [htop]; simp [g66f_P, Matrix.mul_apply]
  have hcn : ∀ g i (k : Fin c), T g (Fin.castAdd c i) (Fin.natAdd d k) = 0 := by
    intro g i k; rw [htop]; simp only [g66f_P, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one,
      mul_zero]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg]; intro h; have := congrArg Fin.val h; simp at this; omega
  have hnc : ∀ g (i : Fin c) k, T g (Fin.natAdd d i) (Fin.castAdd c k) = 0 := by
    intro g i k
    have := congrFun (congrFun (hTstar g⁻¹) (Fin.natAdd d i)) (Fin.castAdd c k)
    rw [inv_inv, Matrix.conjTranspose_apply, hcn] at this
    rw [← this]; simp
  let chi0 : G → Matrix (Fin c) (Fin c) ℂ := fun g i k => T g (Fin.natAdd d i) (Fin.natAdd d k)
  have hT : ∀ g, T g = sumBlock (phi g) (chi0 g) := by
    intro g; ext x y
    refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) y
    · rw [hcc, g66f_sb_cc]
    · rw [hcn, g66f_sb_cn]
    · rw [hnc, g66f_sb_nc]
    · rw [g66f_sb_nn]
  have hT1 : T 1 = 1 := by
    show B * R 1 * B.conjTranspose = 1
    rw [map_one, Matrix.mul_one, hBB]
  let chi : Rep G (Fin c) :=
    { toFun := chi0
      map_one' := by
        have := hT 1
        rw [hT1, ← g66f_sb_one, map_one] at this
        exact (g66f_sb_ext this).2.symm
      map_mul' := by
        intro g h
        have := hTmul g h
        rw [hT, hT, hT, g66f_sb_mul] at this
        exact (g66f_sb_ext this).2 }
  refine ⟨R, hRu, fun g => ⟨pi g, z g, hz1 g, hRform g⟩, hint, chi, ?_, B, hBu, hBtop, ?_,
    g66f_impl M B hBu hBtop⟩
  · intro g
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    have h1 : T g * (T g).conjTranspose = 1 := by
      rw [hTstar, ← hTmul, mul_inv_cancel, hT1]
    rw [hT, g66f_sb_star, g66f_sb_mul, ← g66f_sb_one] at h1
    exact (g66f_sb_ext h1).2
  · intro g
    show sumBlock (phi g) (chi0 g) * B = B * R g
    rw [← hT]
    show B * R g * B.conjTranspose * B = B * R g
    rw [Matrix.mul_assoc, hBB', Matrix.mul_one]

end
