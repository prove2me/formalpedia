-- Prove2me | solution 1 for PatakiRank.Mult.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T18:34:32.976484+00:00
-- url     : https://prove2.me/submissions/be76b012-7423-45df-a697-52e9dd327504

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting

set_option autoImplicit false

open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

/-! Pataki, Theorem 2.2: the rank bound on a face of a multi-block SDP feasible set. -/

open PatakiRank.Mult in
theorem pt22_tri_card {α : Type*} [LinearOrder α] (s : Finset α) :
    ((s ×ˢ s).filter (fun ab : α × α => ab.1 ≤ ab.2)).card = tri s.card := by
  classical
  set A := (s ×ˢ s).filter (fun ab : α × α => ab.1 ≤ ab.2) with hA
  set B := (s ×ˢ s).filter (fun ab : α × α => ab.2 ≤ ab.1) with hB
  have hAB : A.card = B.card := by
    apply Finset.card_bij (fun ab _ => ab.swap)
    · intro ab h
      simp only [hA, hB, Finset.mem_filter, Finset.mem_product, Prod.fst_swap,
        Prod.snd_swap] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · intro x _ z _ h
      exact Prod.swap_injective h
    · intro ab h
      refine ⟨ab.swap, ?_, by simp⟩
      simp only [hA, hB, Finset.mem_filter, Finset.mem_product, Prod.fst_swap,
        Prod.snd_swap] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
  have hU : A ∪ B = s ×ˢ s := by
    ext ab
    simp only [hA, hB, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      rcases le_total ab.1 ab.2 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hI : A ∩ B = s.diag := by
    ext ab
    simp only [hA, hB, Finset.mem_inter, Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨_, h3⟩⟩
      exact ⟨h1.1, le_antisymm h2 h3⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨⟨h1, h2 ▸ h1⟩, h2.le⟩, ⟨⟨h1, h2 ▸ h1⟩, h2.ge⟩⟩
  have key := Finset.card_union_add_card_inter A B
  rw [hU, hI, Finset.card_product, Finset.diag_card] at key
  have htri : 2 * tri s.card = s.card * (s.card + 1) := by
    unfold tri
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self s.card
    rw [hk]
    omega
  have hm : s.card * (s.card + 1) = s.card * s.card + s.card := by ring
  omega

theorem pt22_eigdec {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, ∃ lam : Fin n → ℝ, Uᵀ * U = 1 ∧ (∀ i, 0 ≤ lam i) ∧
      X = U * diagonal lam * Uᵀ ∧ X.rank = Fintype.card {i // lam i ≠ 0} := by
  have hH : X.IsHermitian := hX.isHermitian
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), hH.eigenvalues, ?_,
    hX.eigenvalues_nonneg, ?_, hH.rank_eq_card_non_zero_eigs⟩
  · have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h
  · have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hd : (RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℝ) = hH.eigenvalues := by
      funext i; simp
    rw [hd, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
    exact h

/-- Small symmetric perturbations supported on the support of `lam` keep `U diag(lam) Uᵀ` PSD. -/
theorem pt22_psd_pert {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M)
    (hsupp : ∀ a b, M a b ≠ 0 → lam a ≠ 0 ∧ lam b ≠ 0) :
    ∀ᶠ t in nhds (0 : ℝ), (U * diagonal lam * Uᵀ + t • (U * M * Uᵀ)).PosSemidef := by
  set c : ℝ := ∑ a, (if lam a ≠ 0 then 1 / lam a else 0) with hc
  set C : ℝ := ∑ a, ∑ b, |M a b| with hC
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun a _ => by
    split_ifs
    · exact div_nonneg zero_le_one (hlam a)
    · exact le_refl 0
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _
  have key : ∀ t : ℝ, |t| * (C * c) ≤ 1 → (diagonal lam + t • M).PosSemidef := by
    intro t ht
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · unfold Matrix.IsHermitian
      rw [conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_smul,
        diagonal_transpose, hM]
    · have hstar : star x = x := star_trivial x
      rw [hstar]
      set Λ : ℝ := ∑ a, lam a * x a ^ 2 with hΛ
      set Q : ℝ := ∑ a, ∑ b, x a * M a b * x b with hQ
      have hval : x ⬝ᵥ ((diagonal lam + t • M) *ᵥ x) = Λ + t * Q := by
        rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, hΛ, hQ]
        congr 1
        · simp only [dotProduct, mulVec_diagonal]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
        · congr 1
          simp only [dotProduct, mulVec, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          ring
      rw [hval]
      have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun a _ => mul_nonneg (hlam a) (sq_nonneg _)
      have hsq : ∀ a, lam a ≠ 0 → x a ^ 2 ≤ c * Λ := by
        intro a ha
        have hpos : 0 < lam a := lt_of_le_of_ne (hlam a) (Ne.symm ha)
        have h1 : lam a * x a ^ 2 ≤ Λ :=
          Finset.single_le_sum (f := fun a => lam a * x a ^ 2)
            (fun i _ => mul_nonneg (hlam i) (sq_nonneg _)) (Finset.mem_univ a)
        have h2 : 1 / lam a ≤ c := by
          have h4 : (if lam a ≠ 0 then 1 / lam a else 0) ≤ c :=
            Finset.single_le_sum (f := fun a => if lam a ≠ 0 then 1 / lam a else 0)
            (fun i _ => by
              show 0 ≤ (if lam i ≠ 0 then 1 / lam i else 0)
              split_ifs
              · exact div_nonneg zero_le_one (hlam i)
              · exact le_refl 0) (Finset.mem_univ a)
          rwa [if_pos ha] at h4
        have h3 : x a ^ 2 = 1 / lam a * (lam a * x a ^ 2) := by field_simp
        rw [h3]
        calc 1 / lam a * (lam a * x a ^ 2) ≤ 1 / lam a * Λ :=
              mul_le_mul_of_nonneg_left h1 (div_nonneg zero_le_one hpos.le)
          _ ≤ c * Λ := mul_le_mul_of_nonneg_right h2 hΛ0
      have hterm : ∀ a b, |x a * M a b * x b| ≤ |M a b| * (c * Λ) := by
        intro a b
        by_cases hm : M a b = 0
        · simp [hm]
        obtain ⟨ha, hb⟩ := hsupp a b hm
        have h1 := hsq a ha
        have h2 := hsq b hb
        have h3 : |x a * x b| ≤ c * Λ := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|x a| - |x b|), sq_abs (x a), sq_abs (x b), abs_nonneg (x a),
            abs_nonneg (x b)]
        rw [show x a * M a b * x b = M a b * (x a * x b) by ring, abs_mul]
        exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      have hQb : |Q| ≤ C * (c * Λ) := by
        calc |Q| ≤ ∑ a, |∑ b, x a * M a b * x b| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a, ∑ b, |x a * M a b * x b| :=
              Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a, ∑ b, |M a b| * (c * Λ) :=
              Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
          _ = C * (c * Λ) := by rw [hC, Finset.sum_mul]; simp only [Finset.sum_mul]
      have htQ : |t * Q| ≤ Λ := by
        rw [abs_mul]
        calc |t| * |Q| ≤ |t| * (C * (c * Λ)) := mul_le_mul_of_nonneg_left hQb (abs_nonneg _)
          _ = (|t| * (C * c)) * Λ := by ring
          _ ≤ 1 * Λ := mul_le_mul_of_nonneg_right ht hΛ0
          _ = Λ := one_mul _
      have := neg_abs_le (t * Q)
      linarith
  have hev : ∀ᶠ t in nhds (0 : ℝ), |t| * (C * c) ≤ 1 := by
    have hcont : Continuous fun t : ℝ => |t| * (C * c) := continuous_abs.mul continuous_const
    have : (fun t : ℝ => |t| * (C * c)) 0 < 1 := by simp
    filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const this] with t ht
    exact ht.le
  filter_upwards [hev] with t ht
  have hrw : U * diagonal lam * Uᵀ + t • (U * M * Uᵀ) = U * (diagonal lam + t • M) * Uᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hrw]
  have := (key t ht).mul_mul_conjTranspose_same U
  simpa [conjTranspose_eq_transpose_of_trivial] using this

open PatakiRank.Mult in
/-- `convDim G ≥ dim W` when `G` contains `x0` and a small step from `x0` along every direction
of an injective linear image of `W`. -/
theorem pt22_convDim_ge {E W : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (G : Set E) (x0 : E) (hx0 : x0 ∈ G) (φ : W →ₗ[ℝ] E) (hφ : Function.Injective φ)
    (h : ∀ w, ∃ t : ℝ, 0 < t ∧ x0 + t • φ w ∈ G) :
    (Module.finrank ℝ W : ℤ) ≤ convDim G := by
  classical
  set d := Module.finrank ℝ W with hd
  let b := Module.finBasis ℝ W
  choose t ht htG using fun i : Fin d => h (b i)
  let v : Fin (d + 1) → E := Fin.cons x0 (fun i => x0 + t i • φ (b i))
  have hv : AffineIndependent ℝ v := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ v 0]
    have h1 : LinearIndependent ℝ (fun i => φ (b i)) :=
      b.linearIndependent.map' φ (LinearMap.ker_eq_bot.mpr hφ)
    have hli : LinearIndependent ℝ (fun i => t i • φ (b i)) := by
      convert h1.units_smul (fun i => Units.mk0 (t i) (ht i).ne') using 1
      funext i
      simp [Units.smul_def]
    have hinj : Function.Injective
        (fun x : {x : Fin (d + 1) // x ≠ 0} => (x.1).pred x.2) := by
      intro x z hxz
      exact Subtype.ext ((Fin.pred_inj).mp hxz)
    have hfun : (fun x : {x : Fin (d + 1) // x ≠ 0} => v x -ᵥ v 0) =
        (fun i => t i • φ (b i)) ∘ (fun x : {x : Fin (d + 1) // x ≠ 0} => (x.1).pred x.2) := by
      funext x
      obtain ⟨x, hx⟩ := x
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hx
      simp [v, vsub_eq_sub]
    rw [hfun]
    exact hli.comp _ hinj
  have hmem : ∀ i, v i ∈ G := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [v] using hx0
    · simpa [v] using htG i
  have hbdd : BddAbove {p : ℕ | ∃ v : Fin p → E, (∀ i, v i ∈ G) ∧ AffineIndependent ℝ v} := by
    refine ⟨Module.finrank ℝ E + 1, ?_⟩
    rintro p ⟨v, -, hv⟩
    have h1 := hv.card_le_finrank_succ
    simp only [Fintype.card_fin] at h1
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range v))
    omega
  have hle : d + 1 ≤ sSup {p : ℕ | ∃ v : Fin p → E, (∀ i, v i ∈ G) ∧ AffineIndependent ℝ v} :=
    le_csSup hbdd ⟨v, hmem, hv⟩
  unfold convDim
  omega

theorem pt22_frob_add {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob A (B + C) = frob A B + frob A C := by
  unfold frob
  rw [Matrix.mul_add, Matrix.trace_add]

theorem pt22_frob_smul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    frob A (c • B) = c * frob A B := by
  unfold frob
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Upper-triangle coordinates on `F` give a symmetric matrix supported on `F`. -/
noncomputable def pt22_ML {n : ℕ} (F : Finset (Fin n × Fin n)) :
    (F → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun g := Matrix.of fun i1 i2 => if h : (min i1 i2, max i1 i2) ∈ F then g ⟨_, h⟩ else 0
  map_add' g g' := by
    ext i1 i2
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c g := by
    ext i1 i2
    simp only [Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

theorem pt22_ML_symm {n : ℕ} (F : Finset (Fin n × Fin n)) (g : F → ℝ) :
    (pt22_ML F g)ᵀ = pt22_ML F g := by
  ext i1 i2
  simp only [pt22_ML, LinearMap.coe_mk, AddHom.coe_mk, transpose_apply, of_apply,
    min_comm i2 i1, max_comm i2 i1]

theorem pt22_ML_supp {n : ℕ} (F : Finset (Fin n × Fin n)) (g : F → ℝ) (i1 i2 : Fin n)
    (h : pt22_ML F g i1 i2 ≠ 0) : (min i1 i2, max i1 i2) ∈ F := by
  by_contra hc
  apply h
  simp only [pt22_ML, LinearMap.coe_mk, AddHom.coe_mk, of_apply, dif_neg hc]

theorem pt22_ML_eq_zero {n : ℕ} (F : Finset (Fin n × Fin n)) (hF : ∀ ab ∈ F, ab.1 ≤ ab.2)
    (g : F → ℝ) (hg : pt22_ML F g = 0) : g = 0 := by
  funext ⟨⟨i1, i2⟩, h⟩
  have hab : i1 ≤ i2 := hF _ h
  have := congrFun (congrFun hg i1) i2
  simp only [pt22_ML, LinearMap.coe_mk, AddHom.coe_mk, of_apply, min_eq_left hab,
    max_eq_right hab, dif_pos h, Matrix.zero_apply] at this
  simpa using this

/-- The perturbation map `(g, δy) ↦ ((U_j M(g_j) U_jᵀ)_j, δy)`. -/
noncomputable def pt22_psi {n p q : ℕ} (U : Fin p → Matrix (Fin n) (Fin n) ℝ)
    (F : Fin p → Finset (Fin n × Fin n)) :
    (((Σ j, ↥(F j)) → ℝ) × (Fin q → ℝ)) →ₗ[ℝ]
      ((Fin p → Matrix (Fin n) (Fin n) ℝ) × (Fin q → ℝ)) where
  toFun w := (fun j => U j * pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) * (U j)ᵀ, w.2)
  map_add' w w' := by
    refine Prod.ext (funext fun j => ?_) rfl
    show U j * pt22_ML (F j) ((fun t => w.1 ⟨j, t⟩) + (fun t => w'.1 ⟨j, t⟩)) * (U j)ᵀ =
      U j * pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) * (U j)ᵀ +
        U j * pt22_ML (F j) (fun t => w'.1 ⟨j, t⟩) * (U j)ᵀ
    rw [map_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c w := by
    refine Prod.ext (funext fun j => ?_) rfl
    show U j * pt22_ML (F j) (c • (fun t => w.1 ⟨j, t⟩)) * (U j)ᵀ =
      c • (U j * pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) * (U j)ᵀ)
    rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- The constraint map: the `m₁` trace equations and the upper-triangle entries of the `m₂`
matrix equations. -/
noncomputable def pt22_L0 {n p q m₁ m₂ : ℕ} (Ablk : Fin m₁ → Fin p → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin m₂ → Fin p → ℝ) (D : Fin m₂ → Fin q → Matrix (Fin n) (Fin n) ℝ)
    (Fn : Finset (Fin n × Fin n)) :
    ((Fin p → Matrix (Fin n) (Fin n) ℝ) × (Fin q → ℝ)) →ₗ[ℝ]
      ((Fin m₁ → ℝ) × (Fin m₂ × ↥Fn → ℝ)) where
  toFun v := (fun i => ∑ j, frob (Ablk i j) (v.1 j),
    fun it => (∑ j, a it.1 j • v.1 j + ∑ k, v.2 k • D it.1 k) it.2.1.1 it.2.1.2)
  map_add' v v' := by
    refine Prod.ext (funext fun i => ?_) (funext fun it => ?_)
    · simp only [Prod.fst_add, Pi.add_apply, pt22_frob_add, Finset.sum_add_distrib]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.add_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib]
      ring
  map_smul' c v := by
    refine Prod.ext (funext fun i => ?_) (funext fun it => ?_)
    · simp only [Prod.smul_fst, Pi.smul_apply, pt22_frob_smul, RingHom.id_apply, smul_eq_mul,
        Finset.mul_sum]
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Matrix.add_apply,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;> ring

open PatakiRank.Mult in
theorem solution {n p q m₁ m₂ : ℕ} (Ablk : Fin m₁ → Fin p → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m₁ → ℝ) (a : Fin m₂ → Fin p → ℝ) (D : Fin m₂ → Fin q → Matrix (Fin n) (Fin n) ℝ)
    (Bm : Fin m₂ → Matrix (Fin n) (Fin n) ℝ) (hAblk : ∀ i j, (Ablk i j).IsSymm)
    (hD : ∀ i j, (D i j).IsSymm) (hBm : ∀ i, (Bm i).IsSymm)
    (G : Set ((Fin p → Matrix (Fin n) (Fin n) ℝ) × (Fin q → ℝ)))
    (hG : IsFace (multiFeas Ablk b a D Bm) G)
    (X : Fin p → Matrix (Fin n) (Fin n) ℝ) (y : Fin q → ℝ) (hXy : (X, y) ∈ G) :
    ∑ j, ((tri (X j).rank : ℕ) : ℤ) ≤ ((m₁ + m₂ * tri n : ℕ) : ℤ) - q + convDim G := by
  have hS : (X, y) ∈ multiFeas Ablk b a D Bm := hG.1 hXy
  simp only [multiFeas, Set.mem_setOf_eq] at hS
  obtain ⟨hPSD, hlin1, hlin2⟩ := hS
  choose U lam hUU hlam hXU hrank using fun j => pt22_eigdec (X j) (hPSD j)
  obtain ⟨F, hFdef⟩ : ∃ F : Fin p → Finset (Fin n × Fin n), F = fun j =>
      ((Finset.univ.filter fun i => lam j i ≠ 0) ×ˢ (Finset.univ.filter fun i => lam j i ≠ 0)).filter
        (fun ab : Fin n × Fin n => ab.1 ≤ ab.2) := ⟨_, rfl⟩
  obtain ⟨Fn, hFn⟩ : ∃ Fn : Finset (Fin n × Fin n),
      Fn = ((Finset.univ : Finset (Fin n)) ×ˢ Finset.univ).filter
        (fun ab : Fin n × Fin n => ab.1 ≤ ab.2) := ⟨_, rfl⟩
  have hFle : ∀ j, ∀ ab ∈ F j, ab.1 ≤ ab.2 := by
    intro j ab h
    rw [hFdef] at h
    exact (Finset.mem_filter.mp h).2
  have hFsupp : ∀ j (i1 i2 : Fin n), (min i1 i2, max i1 i2) ∈ F j →
      lam j i1 ≠ 0 ∧ lam j i2 ≠ 0 := by
    intro j i1 i2 h
    rw [hFdef] at h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at h
    rcases le_total i1 i2 with hab | hab
    · rw [min_eq_left hab, max_eq_right hab] at h
      exact ⟨h.1.1, h.1.2⟩
    · rw [min_eq_right hab, max_eq_left hab] at h
      exact ⟨h.1.2, h.1.1⟩
  have hFcard : ∀ j, (F j).card = tri (X j).rank := by
    intro j
    rw [hFdef]
    refine (pt22_tri_card _).trans ?_
    rw [hrank j, Fintype.card_subtype]
  have hFncard : Fn.card = tri n := by
    rw [hFn, pt22_tri_card, Finset.card_univ, Fintype.card_fin]
  set ψ := pt22_psi (q := q) U F with hψ
  set L0 := pt22_L0 Ablk a D Fn with hL0
  set K := LinearMap.ker (L0.comp ψ) with hK
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h1 : ∀ j, pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) = 0 := by
      intro j
      have hj : U j * pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) * (U j)ᵀ = 0 :=
        congrFun (congrArg Prod.fst hw) j
      have hc : (U j)ᵀ * (U j * pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) * (U j)ᵀ) * U j =
          pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) := by
        calc (U j)ᵀ * (U j * pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) * (U j)ᵀ) * U j
            = ((U j)ᵀ * U j) * pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) * ((U j)ᵀ * U j) := by
              simp only [Matrix.mul_assoc]
          _ = pt22_ML (F j) (fun t => w.1 ⟨j, t⟩) := by
              rw [hUU j, Matrix.one_mul, Matrix.mul_one]
      rw [← hc, hj, Matrix.mul_zero, Matrix.zero_mul]
    have h2 : w.2 = 0 := congrArg Prod.snd hw
    refine Prod.ext (funext fun jt => ?_) h2
    obtain ⟨j, t⟩ := jt
    exact congrFun (pt22_ML_eq_zero (F j) (hFle j) _ (h1 j)) t
  have hstep : ∀ w : K, ∃ t : ℝ, 0 < t ∧ (X, y) + t • (ψ.comp K.subtype) w ∈ G := by
    intro w
    set v := ψ w.1 with hv
    have hLv : L0 v = 0 := LinearMap.mem_ker.mp w.2
    have hfro : ∀ i, ∑ j, frob (Ablk i j) (v.1 j) = 0 := fun i =>
      congrFun (congrArg Prod.fst hLv) i
    have hΔs : ∀ j, (v.1 j)ᵀ = v.1 j := by
      intro j
      show (U j * pt22_ML (F j) (fun t => w.1.1 ⟨j, t⟩) * (U j)ᵀ)ᵀ =
        U j * pt22_ML (F j) (fun t => w.1.1 ⟨j, t⟩) * (U j)ᵀ
      rw [transpose_mul, transpose_mul, transpose_transpose, pt22_ML_symm, Matrix.mul_assoc]
    have hR : ∀ i, ∑ j, a i j • v.1 j + ∑ k, v.2 k • D i k = 0 := by
      intro i
      have hent : ∀ ab (hab : ab ∈ Fn),
          (∑ j, a i j • v.1 j + ∑ k, v.2 k • D i k) ab.1 ab.2 = 0 := fun ab hab =>
        congrFun (congrArg Prod.snd hLv) (i, ⟨ab, hab⟩)
      have hDs : ∀ k, (D i k)ᵀ = D i k := fun k => hD i k
      have hsymm : (∑ j, a i j • v.1 j + ∑ k, v.2 k • D i k)ᵀ =
          ∑ j, a i j • v.1 j + ∑ k, v.2 k • D i k := by
        rw [transpose_add, transpose_sum, transpose_sum]
        simp only [transpose_smul, hΔs, hDs]
      ext i1 i2
      rw [Matrix.zero_apply]
      rcases le_total i1 i2 with h | h
      · exact hent (i1, i2) (by rw [hFn]; simp [h])
      · rw [← hsymm, transpose_apply]
        exact hent (i2, i1) (by rw [hFn]; simp [h])
    have hev : ∀ᶠ s in nhds (0 : ℝ), ∀ j, (X j + s • v.1 j).PosSemidef := by
      rw [Filter.eventually_all]
      intro j
      have := pt22_psd_pert (U j) (lam j) (hlam j) (pt22_ML (F j) (fun t => w.1.1 ⟨j, t⟩))
        (pt22_ML_symm _ _) (fun i1 i2 h => hFsupp j i1 i2 (pt22_ML_supp _ _ i1 i2 h))
      rw [← hXU j] at this
      exact this
    have hev2 : ∀ᶠ s in nhds (0 : ℝ), (∀ j, (X j + s • v.1 j).PosSemidef) ∧
        (∀ j, (X j + (-s) • v.1 j).PosSemidef) := by
      refine hev.and ?_
      have hneg : Filter.Tendsto (fun s : ℝ => -s) (nhds 0) (nhds 0) := by
        simpa using (continuous_neg.tendsto (0 : ℝ))
      exact hneg.eventually hev
    obtain ⟨t, ⟨hP, hN⟩, ht0⟩ := ((hev2.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))).and
      (eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
    have hmemS : ∀ s : ℝ, (∀ j, (X j + s • v.1 j).PosSemidef) →
        (X, y) + s • v ∈ multiFeas Ablk b a D Bm := by
      intro s hs
      simp only [multiFeas, Set.mem_setOf_eq]
      refine ⟨fun j => hs j, fun i => ?_, fun i => ?_⟩
      · show ∑ j, frob (Ablk i j) (X j + s • v.1 j) = b i
        simp only [pt22_frob_add, pt22_frob_smul, Finset.sum_add_distrib, ← Finset.mul_sum,
          hfro i, mul_zero, add_zero]
        exact hlin1 i
      · show ∑ j, a i j • (X j + s • v.1 j) + ∑ k, (y k + s * v.2 k) • D i k = Bm i
        have e : ∑ j, a i j • (X j + s • v.1 j) + ∑ k, (y k + s * v.2 k) • D i k =
            (∑ j, a i j • X j + ∑ k, y k • D i k) +
              s • (∑ j, a i j • v.1 j + ∑ k, v.2 k • D i k) := by
          simp only [smul_add, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
            mul_comm s]
          abel
        rw [e, hR i, smul_zero, add_zero]
        exact hlin2 i
    have h1 := hmemS t hP
    have h2 := hmemS (-t) hN
    have hmid : (X, y) = (1 / 2 : ℝ) • ((X, y) + t • v + ((X, y) + (-t) • v)) := by
      module
    exact ⟨t, ht0, (hG.2.2 (X, y) hXy _ h1 _ h2 hmid).1⟩
  have hconv := pt22_convDim_ge G (X, y) hXy (ψ.comp K.subtype)
    (hψinj.comp Subtype.val_injective) hstep
  have hrn := LinearMap.finrank_range_add_finrank_ker (L0.comp ψ)
  have hrange := Submodule.finrank_le (LinearMap.range (L0.comp ψ))
  have hPd : Module.finrank ℝ (((Σ j, ↥(F j)) → ℝ) × (Fin q → ℝ)) =
      ∑ j, tri (X j).rank + q := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_fin]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.card_coe, hFcard j]
  have hCd : Module.finrank ℝ ((Fin m₁ → ℝ) × (Fin m₂ × ↥Fn → ℝ)) = m₁ + m₂ * tri n := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe, hFncard]
  rw [hPd] at hrn
  rw [hCd] at hrange
  have hK' : Module.finrank ℝ K = Module.finrank ℝ (LinearMap.ker (L0.comp ψ)) := rfl
  have hkk : ∑ j, tri (X j).rank + q ≤ Module.finrank ℝ K + (m₁ + m₂ * tri n) := by
    rw [hK']
    linarith
  have hz : ((∑ j, tri (X j).rank : ℕ) : ℤ) + q ≤
      (Module.finrank ℝ K : ℤ) + ((m₁ + m₂ * tri n : ℕ) : ℤ) := by exact_mod_cast hkk
  rw [← Nat.cast_sum]
  linarith
