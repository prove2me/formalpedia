-- Prove2me | solution 1 for TeschlQM.SelfAdjoint.essentiallySelfAdjoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-03T21:08:24.140977+00:00
-- url     : https://prove2.me/submissions/a9f298ef-8e9a-41ed-b6b3-2b66ca7544e2

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_TeschlQM_Shared_IsEssentiallySelfAdjoint
import Theorems.Thm_TeschlQM_SelfAdjoint_selfAdjoint_of_range_eq_top

open scoped InnerProductSpace ComplexConjugate
open Filter Topology

namespace TeschlQM.SelfAdjoint.EssSAAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma mem_rangeAdd_iff (A : H →ₗ.[ℂ] H) (z : ℂ) (x : H) :
    x ∈ rangeAdd A z ↔ ∃ ψ : A.domain, A ψ + z • (ψ : H) = x := by
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨⟨φ, φ.2⟩, ?_⟩
    show A ⟨φ, φ.2⟩ + z • (φ : H) = z • (φ : H) + A ⟨φ, φ.2⟩
    rw [add_comm]
  · rintro ⟨ψ, rfl⟩
    refine ⟨⟨ψ, ψ.2⟩, ?_⟩
    show z • (ψ : H) + A ψ = A ψ + z • (ψ : H)
    rw [add_comm]

/-- For symmetric `A`, `⟪ψ, Aψ⟫` is real. -/
lemma inner_self_apply_im (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (ψ : A.domain) :
    (⟪(ψ : H), A ψ⟫_ℂ).im = 0 := by
  have h := hA.2 ψ ψ
  have h2 : ⟪A ψ, (ψ : H)⟫_ℂ = conj ⟪(ψ : H), A ψ⟫_ℂ := (inner_conj_symm _ _).symm
  rw [h2] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-- `|Im z| ‖ψ‖ ≤ ‖(A + z)ψ‖` for symmetric `A`. -/
lemma im_bound (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ) (ψ : A.domain) :
    |z.im| * ‖(ψ : H)‖ ≤ ‖A ψ + z • (ψ : H)‖ := by
  have hw : (⟪(ψ : H), A ψ + z • (ψ : H)⟫_ℂ).im = z.im * ‖(ψ : H)‖ ^ 2 := by
    rw [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.add_im,
      inner_self_apply_im A hA ψ]
    simp [← Complex.ofReal_pow, Complex.mul_im]
  have h1 : |(⟪(ψ : H), A ψ + z • (ψ : H)⟫_ℂ).im| ≤ ‖(ψ : H)‖ * ‖A ψ + z • (ψ : H)‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  rw [hw, abs_mul, abs_of_nonneg (sq_nonneg ‖(ψ : H)‖), sq] at h1
  rcases (norm_nonneg (ψ : H)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · nlinarith

/-- For symmetric `A`, `‖(A + i)ψ‖ = ‖(A - i)ψ‖`. -/
lemma norm_add_I_eq_norm_sub_I (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (ψ : A.domain) : ‖A ψ + Complex.I • (ψ : H)‖ = ‖A ψ + (-Complex.I) • (ψ : H)‖ := by
  have hre : RCLike.re (⟪A ψ, Complex.I • (ψ : H)⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    have hsym : ⟪A ψ, (ψ : H)⟫_ℂ = ⟪(ψ : H), A ψ⟫_ℂ := (hA.2 ψ ψ).symm
    have hreal : (⟪A ψ, (ψ : H)⟫_ℂ).im = 0 := by
      rw [hsym]; exact inner_self_apply_im A hA ψ
    simp [hreal]
  have h1 : ‖A ψ + Complex.I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), hre, norm_smul, Complex.norm_I, one_mul]; ring
  have h2 : ‖A ψ + (-Complex.I) • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := by
    rw [neg_smul, ← sub_eq_add_neg, norm_sub_sq (𝕜 := ℂ), hre, norm_smul, Complex.norm_I,
      one_mul]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h1.trans h2.symm)

/-- `A + z` as a linear map on `𝔇(A)`. -/
noncomputable def addZ (A : H →ₗ.[ℂ] H) (z : ℂ) : A.domain →ₗ[ℂ] H :=
  A.toFun + z • A.domain.subtype

lemma addZ_apply (A : H →ₗ.[ℂ] H) (z : ℂ) (ψ : A.domain) :
    addZ A z ψ = A ψ + z • (ψ : H) := rfl

lemma range_addZ (A : H →ₗ.[ℂ] H) (z : ℂ) : LinearMap.range (addZ A z) = rangeAdd A z := by
  ext x
  rw [mem_rangeAdd_iff, LinearMap.mem_range]
  rfl

lemma addZ_injective (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ)
    (hz : z.im ≠ 0) : Function.Injective (addZ A z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ψ hψ
  have := im_bound A hA z ψ
  rw [← addZ_apply, hψ, norm_zero] at this
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  have : ‖(ψ : H)‖ ≤ 0 := by nlinarith [norm_nonneg (ψ : H)]
  exact Subtype.ext (norm_le_zero_iff.mp this)

lemma adjoint_apply_of_eq (A T : H →ₗ.[ℂ] H) (hT : T = A) (x : H) (h1 : x ∈ T.domain)
    (h2 : x ∈ A.domain) : T ⟨x, h1⟩ = A ⟨x, h2⟩ := by
  subst hT; rfl

variable [CompleteSpace H]

/-- For a self-adjoint `B` and non-real `z`, `Ran(B + z) = ℌ`. -/
lemma rangeAdd_eq_top_of_isSelfAdjoint (B : H →ₗ.[ℂ] H) (hSA : IsSelfAdjoint B) (z : ℂ)
    (hz : z.im ≠ 0) : rangeAdd B z = ⊤ := by
  have hdense : Dense (B.domain : Set H) := hSA.dense_domain
  have hB : TeschlQM.Shared.IsSymmetric B := by
    refine ⟨hdense, fun φ ψ => ?_⟩
    have hadj := LinearPMap.adjoint_isFormalAdjoint hdense (T := B)
    have h1 := hadj ⟨φ, by rw [LinearPMap.isSelfAdjoint_def.mp hSA]; exact φ.2⟩ ψ
    rw [adjoint_apply_of_eq B B.adjoint (LinearPMap.isSelfAdjoint_def.mp hSA) φ _ φ.2] at h1
    exact h1.symm
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  -- the range is closed
  have hcl : IsClosed (rangeAdd B z : Set H) := by
    refine IsSeqClosed.isClosed fun {y} {y₀} hy hlim => ?_
    have hy' : ∀ n, ∃ ψ : B.domain, B ψ + z • (ψ : H) = y n := fun n =>
      (mem_rangeAdd_iff B _ _).mp (hy n)
    choose ψ hψ using hy'
    have hcauchy : CauchySeq fun n => (ψ n : H) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq (|z.im| * ε) (mul_pos hpos hε)
      refine ⟨N, fun m hm k hk => ?_⟩
      have h1 := im_bound B hB z (ψ m - ψ k)
      have h2 : B (ψ m - ψ k) + z • ((ψ m - ψ k : B.domain) : H) = y m - y k := by
        rw [← hψ m, ← hψ k, LinearPMap.map_sub]
        simp only [Submodule.coe_sub, smul_sub]
        abel
      rw [h2] at h1
      rw [dist_eq_norm]
      have h3 := hN m hm k hk
      rw [dist_eq_norm] at h3
      simp only [Submodule.coe_sub] at h1
      by_contra! hcon
      nlinarith
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hBψ : Tendsto (fun n => B (ψ n)) atTop (𝓝 (y₀ - z • x)) := by
      have : (fun n => B (ψ n)) = fun n => y n - z • (ψ n : H) := by
        funext n; rw [← hψ n]; abel
      rw [this]
      exact hlim.sub (hx.const_smul z)
    have hmem : (x, y₀ - z • x) ∈ B.graph := by
      have hcl : IsClosed (B.graph : Set (H × H)) := hSA.isClosed
      refine hcl.mem_of_tendsto (hx.prodMk_nhds hBψ) (Eventually.of_forall fun n => ?_)
      exact (LinearPMap.mem_graph_iff B).mpr ⟨ψ n, rfl, rfl⟩
    obtain ⟨x', hx1, hx2⟩ := (LinearPMap.mem_graph_iff B).mp hmem
    refine (mem_rangeAdd_iff B _ _).mpr ⟨x', ?_⟩
    rw [hx2, hx1]
    simp
  -- the orthogonal complement is trivial
  have horth : (rangeAdd B z)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro φ hφ
    have hφ' : ∀ ψ : B.domain, ⟪B ψ + z • (ψ : H), φ⟫_ℂ = 0 := fun ψ =>
      (Submodule.mem_orthogonal _ _).mp hφ _ ((mem_rangeAdd_iff B _ _).mpr ⟨ψ, rfl⟩)
    have key : ∀ ψ : B.domain, ⟪(-conj z) • φ, (ψ : H)⟫_ℂ = ⟪φ, B ψ⟫_ℂ := by
      intro ψ
      have e : ⟪B ψ, φ⟫_ℂ = -(conj z * ⟪(ψ : H), φ⟫_ℂ) := by
        have := hφ' ψ
        rw [inner_add_left, inner_smul_left, add_eq_zero_iff_eq_neg] at this
        exact this
      rw [inner_smul_left, map_neg, Complex.conj_conj, ← inner_conj_symm φ (B ψ), e, map_neg,
        map_mul, Complex.conj_conj, inner_conj_symm, neg_mul]
    have hadj : φ ∈ B.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨(-conj z) • φ, key⟩
    have hval : B.adjoint ⟨φ, hadj⟩ = (-conj z) • φ :=
      LinearPMap.adjoint_apply_eq hdense _ key
    have hdom : φ ∈ B.domain := by
      have : B.adjoint.domain = B.domain := by rw [LinearPMap.isSelfAdjoint_def.mp hSA]
      exact this ▸ hadj
    have hBφ : B ⟨φ, hdom⟩ = (-conj z) • φ := by
      rw [← adjoint_apply_of_eq B B.adjoint (LinearPMap.isSelfAdjoint_def.mp hSA) φ hadj hdom,
        hval]
    have := im_bound B hB (conj z) ⟨φ, hdom⟩
    simp only at this
    rw [hBφ, neg_smul, neg_add_cancel, norm_zero, Complex.conj_im, abs_neg] at this
    have : ‖φ‖ ≤ 0 := by nlinarith [norm_nonneg φ]
    exact norm_le_zero_iff.mp this
  have := (Submodule.topologicalClosure_eq_top_iff (K := rangeAdd B z)).mpr horth
  rwa [IsClosed.submodule_topologicalClosure_eq hcl] at this


/-- A closed operator with `c ‖ψ‖ ≤ ‖(B + z)ψ‖`, `c > 0`, has closed `Ran(B + z)`. -/
lemma isClosed_rangeAdd_of_bound (B : H →ₗ.[ℂ] H) (hBc : B.IsClosed) (z : ℂ) (c : ℝ) (hc : 0 < c)
    (hb : ∀ ψ : B.domain, c * ‖(ψ : H)‖ ≤ ‖B ψ + z • (ψ : H)‖) :
    IsClosed (rangeAdd B z : Set H) := by
  refine IsSeqClosed.isClosed fun {y} {y₀} hy hlim => ?_
  have hy' : ∀ n, ∃ ψ : B.domain, B ψ + z • (ψ : H) = y n := fun n =>
    (mem_rangeAdd_iff B _ _).mp (hy n)
  choose ψ hψ using hy'
  have hcauchy : CauchySeq fun n => (ψ n : H) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq (c * ε) (mul_pos hc hε)
    refine ⟨N, fun m hm k hk => ?_⟩
    have h1 := hb (ψ m - ψ k)
    have h2 : B (ψ m - ψ k) + z • ((ψ m - ψ k : B.domain) : H) = y m - y k := by
      rw [← hψ m, ← hψ k, LinearPMap.map_sub]
      simp only [Submodule.coe_sub, smul_sub]
      abel
    rw [h2] at h1
    rw [dist_eq_norm]
    have h3 := hN m hm k hk
    rw [dist_eq_norm] at h3
    simp only [Submodule.coe_sub] at h1
    by_contra! hcon
    nlinarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hBψ : Tendsto (fun n => B (ψ n)) atTop (𝓝 (y₀ - z • x)) := by
    have : (fun n => B (ψ n)) = fun n => y n - z • (ψ n : H) := by
      funext n; rw [← hψ n]; abel
    rw [this]
    exact hlim.sub (hx.const_smul z)
  have hmem : (x, y₀ - z • x) ∈ B.graph := by
    have hcl : IsClosed (B.graph : Set (H × H)) := hBc
    refine hcl.mem_of_tendsto (hx.prodMk_nhds hBψ) (Eventually.of_forall fun n => ?_)
    exact (LinearPMap.mem_graph_iff B).mpr ⟨ψ n, rfl, rfl⟩
  obtain ⟨x', hx1, hx2⟩ := (LinearPMap.mem_graph_iff B).mp hmem
  refine (mem_rangeAdd_iff B _ _).mpr ⟨x', ?_⟩
  rw [hx2, hx1]
  simp

/-- A symmetric operator is closable (it has the closed extension `A*`). -/
lemma isClosable_of_isSymmetric (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    A.IsClosable := by
  have hformal : A.IsFormalAdjoint A := fun x y => (hA.2 x y).symm
  exact LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨A.adjoint, LinearPMap.adjoint_isClosed hA.1, hformal.le_adjoint hA.1⟩

/-- The graph of the closure is the closure of the graph. -/
lemma mem_closure_graph (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (x : A.closure.domain) : ((x : H), A.closure x) ∈ closure (A.graph : Set (H × H)) := by
  rw [← Submodule.topologicalClosure_coe,
    (isClosable_of_isSymmetric A hA).graph_closure_eq_closure_graph]
  exact LinearPMap.mem_graph A.closure x

/-- The closure of a symmetric operator is symmetric. -/
lemma closure_isSymmetric (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    TeschlQM.Shared.IsSymmetric A.closure := by
  refine ⟨hA.1.mono (A.le_closure).1, fun x₁ x₂ => ?_⟩
  let Q : Set ((H × H) × (H × H)) := {p | ⟪p.1.1, p.2.2⟫_ℂ = ⟪p.1.2, p.2.1⟫_ℂ}
  have hQ : IsClosed Q := isClosed_eq
    ((continuous_fst.comp continuous_fst).inner (continuous_snd.comp continuous_snd))
    ((continuous_snd.comp continuous_fst).inner (continuous_fst.comp continuous_snd))
  have hsub : (A.graph : Set (H × H)) ×ˢ (A.graph : Set (H × H)) ⊆ Q := by
    rintro ⟨g₁, g₂⟩ ⟨h₁, h₂⟩
    obtain ⟨ψ₁, e₁, f₁⟩ := (LinearPMap.mem_graph_iff A).mp h₁
    obtain ⟨ψ₂, e₂, f₂⟩ := (LinearPMap.mem_graph_iff A).mp h₂
    show ⟪g₁.1, g₂.2⟫_ℂ = ⟪g₁.2, g₂.1⟫_ℂ
    rw [← e₁, ← f₁, ← e₂, ← f₂]
    exact hA.2 ψ₁ ψ₂
  have hmem : (((x₁ : H), A.closure x₁), ((x₂ : H), A.closure x₂)) ∈ Q := by
    have := hQ.closure_subset_iff.mpr hsub
    rw [closure_prod_eq] at this
    exact this ⟨mem_closure_graph A hA x₁, mem_closure_graph A hA x₂⟩
  exact hmem

/-- A lower bound `c ‖ψ‖ ≤ ‖(A + z)ψ‖` passes to the closure. -/
lemma closure_bound (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ) (c : ℝ)
    (hb : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ + z • (ψ : H)‖) (x : A.closure.domain) :
    c * ‖(x : H)‖ ≤ ‖A.closure x + z • (x : H)‖ := by
  let P : Set (H × H) := {g | c * ‖g.1‖ ≤ ‖g.2 + z • g.1‖}
  have hP : IsClosed P := isClosed_le (continuous_const.mul continuous_fst.norm)
    (continuous_snd.add (continuous_fst.const_smul z)).norm
  have hsub : (A.graph : Set (H × H)) ⊆ P := by
    intro g hg
    obtain ⟨ψ, e, f⟩ := (LinearPMap.mem_graph_iff A).mp hg
    show c * ‖g.1‖ ≤ ‖g.2 + z • g.1‖
    rw [← e, ← f]
    exact hb ψ
  exact hP.closure_subset_iff.mpr hsub (mem_closure_graph A hA x)

/-- `Ran(Ā + z) ⊆ closure Ran(A + z)`. -/
lemma rangeAdd_closure_subset (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ) :
    (rangeAdd A.closure z : Set H) ⊆ closure (rangeAdd A z : Set H) := by
  intro y hy
  obtain ⟨x, rfl⟩ := (mem_rangeAdd_iff A.closure _ _).mp hy
  have hF : Continuous fun g : H × H => g.2 + z • g.1 :=
    continuous_snd.add (continuous_fst.const_smul z)
  have hmaps : Set.MapsTo (fun g : H × H => g.2 + z • g.1) (A.graph : Set (H × H))
      (rangeAdd A z : Set H) := by
    intro g hg
    obtain ⟨ψ, e, f⟩ := (LinearPMap.mem_graph_iff A).mp hg
    show g.2 + z • g.1 ∈ (rangeAdd A z : Set H)
    rw [← e, ← f]
    exact (mem_rangeAdd_iff A _ _).mpr ⟨ψ, rfl⟩
  have h := map_mem_closure (f := fun g : H × H => g.2 + z • g.1) hF
    (mem_closure_graph A hA x) hmaps
  exact h

/-- `Ker(A* + z) = Ran(A + z*)^⊥` for densely defined `A`. -/
lemma kerAdd_adjoint_eq (A : H →ₗ.[ℂ] H) (hd : Dense (A.domain : Set H)) (z : ℂ) :
    kerAdd A.adjoint z = (rangeAdd A (conj z))ᗮ := by
  ext ψ
  constructor
  · intro hψ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hψ
    have hy' : z • (y : H) + A.adjoint ⟨y, y.2⟩ = 0 := hy
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨φ, rfl⟩ := (mem_rangeAdd_iff A _ _).mp hu
    have hadj := LinearPMap.adjoint_isFormalAdjoint hd (T := A) ⟨y, y.2⟩ φ
    simp only at hadj
    have e : A.adjoint ⟨y, y.2⟩ = -(z • (y : H)) := eq_neg_of_add_eq_zero_right hy'
    show ⟪A φ + conj z • (φ : H), (y : H)⟫_ℂ = 0
    rw [inner_add_left, ← inner_conj_symm (A φ) (y : H), ← hadj, e]
    simp [inner_smul_left]
  · intro hψ
    have hψ' : ∀ φ : A.domain, ⟪A φ + conj z • (φ : H), ψ⟫_ℂ = 0 := fun φ =>
      (Submodule.mem_orthogonal _ _).mp hψ _ ((mem_rangeAdd_iff A _ _).mpr ⟨φ, rfl⟩)
    have key : ∀ φ : A.domain, ⟪(-z) • ψ, (φ : H)⟫_ℂ = ⟪ψ, A φ⟫_ℂ := by
      intro φ
      have e : ⟪A φ, ψ⟫_ℂ = -(z * ⟪(φ : H), ψ⟫_ℂ) := by
        have := hψ' φ
        rw [inner_add_left, inner_smul_left, Complex.conj_conj, add_eq_zero_iff_eq_neg] at this
        exact this
      rw [inner_smul_left, ← inner_conj_symm ψ (A φ), e]
      simp only [map_neg, map_mul, inner_conj_symm]
      ring
    have hadj : ψ ∈ A.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨(-z) • ψ, key⟩
    have hval : A.adjoint ⟨ψ, hadj⟩ = (-z) • ψ := LinearPMap.adjoint_apply_eq hd _ key
    refine Submodule.mem_map.mpr ⟨⟨ψ, hadj⟩, ?_, rfl⟩
    show z • ψ + A.adjoint ⟨ψ, hadj⟩ = 0
    rw [hval, neg_smul, add_neg_cancel]

lemma kerAdd_adjoint_eq_bot_iff (A : H →ₗ.[ℂ] H) (hd : Dense (A.domain : Set H)) (z : ℂ) :
    kerAdd A.adjoint z = ⊥ ↔ (rangeAdd A (conj z)).topologicalClosure = ⊤ := by
  rw [kerAdd_adjoint_eq A hd, Submodule.topologicalClosure_eq_top_iff]

/-- Sufficient condition: lower bounds at `z` and `z*` plus dense ranges give essential
self-adjointness (Lemma 2.3 applied to the closure). -/
lemma essSA_of_dense (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ) (c : ℝ)
    (hc : 0 < c) (hb : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ + z • (ψ : H)‖)
    (hb' : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ + conj z • (ψ : H)‖)
    (h1 : (rangeAdd A z).topologicalClosure = ⊤)
    (h2 : (rangeAdd A (conj z)).topologicalClosure = ⊤) :
    TeschlQM.Shared.IsEssentiallySelfAdjoint A := by
  have hcl := (isClosable_of_isSymmetric A hA).closure_isClosed
  have htop : ∀ w : ℂ, (∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ + w • (ψ : H)‖) →
      (rangeAdd A w).topologicalClosure = ⊤ → rangeAdd A.closure w = ⊤ := by
    intro w hbw hw
    have hclosed := isClosed_rangeAdd_of_bound A.closure hcl w c hc (closure_bound A hA w c hbw)
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ (rangeAdd A w).topologicalClosure := by rw [hw]; trivial
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hy
    have hsub : (rangeAdd A w : Set H) ⊆ (rangeAdd A.closure w : Set H) := by
      intro u hu
      obtain ⟨ψ, rfl⟩ := (mem_rangeAdd_iff A _ _).mp hu
      have hψ : (ψ : H) ∈ A.closure.domain := (A.le_closure).1 ψ.2
      have hAψ : A ψ = A.closure ⟨ψ, hψ⟩ := (A.le_closure).2 rfl
      exact (mem_rangeAdd_iff A.closure _ _).mpr ⟨⟨ψ, hψ⟩, by rw [← hAψ]⟩
    exact hclosed.closure_subset_iff.mpr hsub hy
  exact selfAdjoint_of_range_eq_top A.closure (closure_isSymmetric A hA) z (htop z hb h1)
    (htop (conj z) hb' h2)

/-- Necessary condition: if `Ā` is self-adjoint then `Ran(A ± i)` are dense. -/
lemma dense_of_essSA (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (hE : TeschlQM.Shared.IsEssentiallySelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    (rangeAdd A z).topologicalClosure = ⊤ := by
  have h := rangeAdd_eq_top_of_isSelfAdjoint A.closure hE z hz
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ rangeAdd A.closure z := by rw [h]; trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact rangeAdd_closure_subset A hA z hy

omit [CompleteSpace H] in
/-- For nonnegative `A` and real `z > 0`: `z ‖ψ‖ ≤ ‖(A + z)ψ‖`. -/
lemma re_bound (A : H →ₗ.[ℂ] H) (hpos : ∀ ψ : A.domain, 0 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) (z : ℂ)
    (hz : z.im = 0) (ψ : A.domain) : z.re * ‖(ψ : H)‖ ≤ ‖A ψ + z • (ψ : H)‖ := by
  have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [hz])
  have hw : (⟪(ψ : H), A ψ + z • (ψ : H)⟫_ℂ).re = (⟪(ψ : H), A ψ⟫_ℂ).re + z.re * ‖(ψ : H)‖ ^ 2 := by
    rw [inner_add_right, inner_smul_right, Complex.add_re, hz', Complex.re_ofReal_mul,
      Complex.ofReal_re]
    have hn : (⟪(ψ : H), (ψ : H)⟫_ℂ).re = ‖(ψ : H)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [hn]
  have h1 : (⟪(ψ : H), A ψ + z • (ψ : H)⟫_ℂ).re ≤ ‖(ψ : H)‖ * ‖A ψ + z • (ψ : H)‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [hw] at h1
  have h2 := hpos ψ
  rcases (norm_nonneg (ψ : H)).eq_or_lt with h0 | hp
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have : z.re * ‖(ψ : H)‖ * ‖(ψ : H)‖ ≤ ‖A ψ + z • (ψ : H)‖ * ‖(ψ : H)‖ := by nlinarith
    exact le_of_mul_le_mul_right this hp

end TeschlQM.SelfAdjoint.EssSAAux

open TeschlQM.SelfAdjoint TeschlQM.SelfAdjoint.EssSAAux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    (TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
      ∃ z : ℂ, z.im ≠ 0 ∧ (rangeAdd A z).topologicalClosure = ⊤ ∧
        (rangeAdd A (conj z)).topologicalClosure = ⊤) ∧
    (TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
      ∃ z : ℂ, z.im ≠ 0 ∧ kerAdd A.adjoint z = ⊥ ∧ kerAdd A.adjoint (conj z) = ⊥) ∧
    ((∀ ψ : A.domain, 0 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) →
      (TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
        ∃ z : ℂ, (z.im ≠ 0 ∨ (z.im = 0 ∧ 0 < z.re)) ∧ (rangeAdd A z).topologicalClosure = ⊤ ∧
          (rangeAdd A (conj z)).topologicalClosure = ⊤) ∧
      (TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
        ∃ z : ℂ, (z.im ≠ 0 ∨ (z.im = 0 ∧ 0 < z.re)) ∧ kerAdd A.adjoint z = ⊥ ∧
          kerAdd A.adjoint (conj z) = ⊥)) := by
  have hI : Complex.I.im ≠ 0 := by simp
  have hker : ∀ z : ℂ, (kerAdd A.adjoint z = ⊥ ∧ kerAdd A.adjoint (conj z) = ⊥) ↔
      ((rangeAdd A z).topologicalClosure = ⊤ ∧ (rangeAdd A (conj z)).topologicalClosure = ⊤) := by
    intro z
    rw [kerAdd_adjoint_eq_bot_iff A hA.1, kerAdd_adjoint_eq_bot_iff A hA.1, Complex.conj_conj]
    exact and_comm
  -- the nonreal case
  have hnonreal : ∀ z : ℂ, z.im ≠ 0 → (rangeAdd A z).topologicalClosure = ⊤ →
      (rangeAdd A (conj z)).topologicalClosure = ⊤ →
      TeschlQM.Shared.IsEssentiallySelfAdjoint A := by
    intro z hz h1 h2
    refine essSA_of_dense A hA z |z.im| (abs_pos.mpr hz) (im_bound A hA z) (fun ψ => ?_) h1 h2
    have := im_bound A hA (conj z) ψ
    rwa [Complex.conj_im, abs_neg] at this
  have hfwd : TeschlQM.Shared.IsEssentiallySelfAdjoint A →
      (rangeAdd A Complex.I).topologicalClosure = ⊤ ∧
        (rangeAdd A (conj Complex.I)).topologicalClosure = ⊤ :=
    fun hE => ⟨dense_of_essSA A hA hE _ hI, dense_of_essSA A hA hE _ (by simp)⟩
  have part1 : TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
      ∃ z : ℂ, z.im ≠ 0 ∧ (rangeAdd A z).topologicalClosure = ⊤ ∧
        (rangeAdd A (conj z)).topologicalClosure = ⊤ :=
    ⟨fun hE => ⟨Complex.I, hI, hfwd hE⟩, fun ⟨z, hz, h1, h2⟩ => hnonreal z hz h1 h2⟩
  refine ⟨part1, ?_, fun hpos => ?_⟩
  · rw [part1]
    exact exists_congr fun z => and_congr_right fun _ => (hker z).symm
  · have part3 : TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
        ∃ z : ℂ, (z.im ≠ 0 ∨ (z.im = 0 ∧ 0 < z.re)) ∧ (rangeAdd A z).topologicalClosure = ⊤ ∧
          (rangeAdd A (conj z)).topologicalClosure = ⊤ := by
      constructor
      · intro hE
        exact ⟨Complex.I, Or.inl hI, hfwd hE⟩
      · rintro ⟨z, hz | ⟨hz0, hzpos⟩, h1, h2⟩
        · exact hnonreal z hz h1 h2
        · refine essSA_of_dense A hA z z.re hzpos (re_bound A hpos z hz0) (fun ψ => ?_) h1 h2
          have := re_bound A hpos (conj z) (by rw [Complex.conj_im, hz0, neg_zero]) ψ
          rwa [Complex.conj_re] at this
    refine ⟨part3, ?_⟩
    rw [part3]
    exact exists_congr fun z => and_congr_right fun _ => (hker z).symm
