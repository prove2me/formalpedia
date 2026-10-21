-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P25.representationKernel_closed_and_quotientBanach
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:35:35.841697+00:00
-- url     : https://prove2.me/submissions/236db535-1ecb-4536-a4a7-26a1cbbd18c1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25
noncomputable section

open Set Filter Topology

open scoped Classical ENNReal

open QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

lemma g61b_limit_le {t C X Y : ℝ} (h : ∀ ε : ℝ, 0 < ε → t ≤ C * (X + ε) * (Y + ε)) :
    t ≤ C * X * Y := by
  have hc : Tendsto (fun ε : ℝ => C * (X + ε) * (Y + ε)) (𝓝[>] 0) (𝓝 (C * (X + 0) * (Y + 0))) :=
    ((by fun_prop : Continuous (fun ε : ℝ => C * (X + ε) * (Y + ε))).tendsto 0).mono_left
      nhdsWithin_le_nhds
  simp only [add_zero] at hc
  exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)

theorem solution
    {K : Type u} [RCLike K]
    {g : Type v} [NormedAddCommGroup g] [NormedSpace K g] [CompleteSpace g]
    {V : Type w} [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul K V] [T2Space V]
    (b : ContinuousLieBracket K g)
    (rho : g →ₗ[K] Module.End K V)
    (hLie : ∀ (x y : g) (v : V),
      rho (b.bracket x y) v = rho x (rho y v) - rho y (rho x v))
    (hStrong : StronglyContinuous (fun x v => rho x v)) :
    (∀ (x y : g), y ∈ rho.ker → b.bracket x y ∈ rho.ker) ∧
    IsClosed (rho.ker : Set g) ∧
    (let Q := g ⧸ rho.ker
     CompleteSpace Q ∧ (∀ z : Q, ‖z‖ = 0 → z = 0) ∧
       ∃ (quotientBracket : ContinuousLieBracket K Q)
         (quotientRho : Q →ₗ[K] Module.End K V),
         (∀ x y : g,
           quotientBracket.bracket (rho.ker.mkQ x) (rho.ker.mkQ y) =
             rho.ker.mkQ (b.bracket x y)) ∧
         (∀ x : g, quotientRho (rho.ker.mkQ x) = rho x) ∧
         Function.Injective quotientRho ∧
         (∀ (x y : Q) (v : V),
           quotientRho (quotientBracket.bracket x y) v =
             quotientRho x (quotientRho y v) - quotientRho y (quotientRho x v)) ∧
         StronglyContinuous (fun x v => quotientRho x v)) := by
  set N := LinearMap.ker rho with hN
  have hR : ∀ x y : g, y ∈ N → b.bracket x y ∈ N := by
    intro x y hy
    rw [hN, LinearMap.mem_ker] at hy ⊢
    ext v
    rw [hLie]; simp [hy]
  have hL : ∀ x y : g, x ∈ N → b.bracket x y ∈ N := by
    intro x y hx
    rw [b.skew]; exact N.neg_mem (hR y x hx)
  have hclosed : IsClosed (N : Set g) := by
    have : (N : Set g) = ⋂ v : V, (fun x => rho x v) ⁻¹' {0} := by
      ext x; simp [hN, LinearMap.ext_iff]
    rw [this]
    exact isClosed_iInter fun v => (isClosed_singleton).preimage (hStrong v)
  refine ⟨hR, hclosed, ?_⟩
  intro Q
  refine ⟨inferInstance, ?_, ?_⟩
  · intro z hz
    obtain ⟨m, rfl⟩ := N.mkQ_surjective z
    have := (QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure (S := N.toAddSubgroup) (m := m)).1 hz
    rw [show ((N.toAddSubgroup : Set g)) = (N : Set g) from rfl, hclosed.closure_eq] at this
    exact (Submodule.Quotient.mk_eq_zero N).2 this
  -- bracket
  let B0 : g → (g ⧸ N) →ₗ[K] (g ⧸ N) := fun x =>
    N.liftQ (N.mkQ ∘ₗ (b.bracket x : g →L[K] g).toLinearMap) (by
      intro y hy
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_coe, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hR x y hy)
  have B0_mk : ∀ x y : g, B0 x (N.mkQ y) = N.mkQ (b.bracket x y) := fun x y => rfl
  let B1 : g →ₗ[K] (g ⧸ N) →ₗ[K] (g ⧸ N) :=
    { toFun := B0
      map_add' := fun x y => by
        apply Submodule.linearMap_qext; ext w
        change B0 (x+y) (N.mkQ w) = B0 x (N.mkQ w) + B0 y (N.mkQ w)
        simp only [B0_mk, map_add, ContinuousLinearMap.add_apply]
      map_smul' := fun c x => by
        apply Submodule.linearMap_qext; ext w
        change B0 (c • x) (N.mkQ w) = c • B0 x (N.mkQ w)
        rw [B0_mk, B0_mk, map_smul, ContinuousLinearMap.smul_apply, map_smul] }
  let B2 : (g ⧸ N) →ₗ[K] (g ⧸ N) →ₗ[K] (g ⧸ N) :=
    N.liftQ B1 (by
      intro x hx
      rw [LinearMap.mem_ker]
      apply Submodule.linearMap_qext; ext w
      change B0 x (N.mkQ w) = 0
      rw [B0_mk]; simpa using hL x w hx)
  have B2_mk : ∀ x y : g, B2 (N.mkQ x) (N.mkQ y) = N.mkQ (b.bracket x y) := fun x y => rfl
  let C : ℝ := ‖b.bracket‖
  have hbound : ∀ x y : g ⧸ N, ‖B2 x y‖ ≤ C * ‖x‖ * ‖y‖ := by
    intro x y
    apply g61b_limit_le
    intro ε hε
    obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hε
    obtain ⟨c, rfl, hc⟩ := Submodule.Quotient.norm_mk_lt y hε
    have e1 := B2_mk a c
    simp only [Submodule.mkQ_apply] at e1
    rw [e1]
    calc ‖(Submodule.Quotient.mk (b.bracket a c) : g ⧸ N)‖ ≤ ‖b.bracket a c‖ :=
          Submodule.Quotient.norm_mk_le _ _
      _ ≤ ‖b.bracket a‖ * ‖c‖ := (b.bracket a).le_opNorm c
      _ ≤ C * ‖a‖ * ‖c‖ := by
          apply mul_le_mul_of_nonneg_right (b.bracket.le_opNorm a) (norm_nonneg _)
      _ ≤ C * (‖(Submodule.Quotient.mk a : g ⧸ N)‖ + ε) *
            (‖(Submodule.Quotient.mk c : g ⧸ N)‖ + ε) := by
          have hC : 0 ≤ C := norm_nonneg b.bracket
          gcongr
  let Bq : (g ⧸ N) →L[K] (g ⧸ N) →L[K] (g ⧸ N) := LinearMap.mkContinuous₂ B2 C hbound
  have Bq_mk : ∀ x y : g, Bq (N.mkQ x) (N.mkQ y) = N.mkQ (b.bracket x y) := fun x y => rfl
  let qb : ContinuousLieBracket K (g ⧸ N) :=
    { bracket := Bq
      skew := by
        intro x y
        obtain ⟨x, rfl⟩ := N.mkQ_surjective x
        obtain ⟨y, rfl⟩ := N.mkQ_surjective y
        rw [Bq_mk, Bq_mk, b.skew, map_neg]
      jacobi := by
        intro x y z
        obtain ⟨x, rfl⟩ := N.mkQ_surjective x
        obtain ⟨y, rfl⟩ := N.mkQ_surjective y
        obtain ⟨z, rfl⟩ := N.mkQ_surjective z
        simp only [Bq_mk, ← map_add, b.jacobi, map_zero] }
  let qr : (g ⧸ N) →ₗ[K] Module.End K V := N.liftQ rho le_rfl
  have qr_mk : ∀ x : g, qr (N.mkQ x) = rho x := fun x => rfl
  refine ⟨qb, qr, Bq_mk, qr_mk, ?_, ?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  · intro x y v
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    change qr (Bq (N.mkQ x) (N.mkQ y)) v = _
    rw [Bq_mk, qr_mk, qr_mk, qr_mk, hLie]
  · intro v
    rw [(Submodule.isOpenQuotientMap_mkQ N).isQuotientMap.continuous_iff]
    exact hStrong v
