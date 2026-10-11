-- Prove2me | solution 1 for ProjReflGrad.Weak.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T05:53:16.574989+00:00
-- url     : https://prove2.me/submissions/eb14d74a-c6c3-4f98-ad6c-2da6ba1ad040

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

namespace OpialKit

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Weak convergence, in the form every mission uses. -/
def WLim (x : ℕ → H) (p : H) : Prop :=
  ∀ v : H, Tendsto (fun n => inner ℝ (x n) v) atTop (𝓝 (inner ℝ p v))

/-- K1. Bounded sequences in a real Hilbert space have weakly convergent subsequences. -/
theorem exists_wlim_subseq [CompleteSpace H] (x : ℕ → H) (C : ℝ) (hC : ∀ n, ‖x n‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : H, WLim (x ∘ φ) p := by
  set M : Submodule ℝ H := (Submodule.span ℝ (Set.range x)).topologicalClosure with hMdef
  have hMc : IsClosed (M : Set H) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace M := hMc.completeSpace_coe
  have hsep : TopologicalSpace.IsSeparable (M : Set H) := by
    rw [hMdef, Submodule.topologicalClosure_coe]
    exact (Set.countable_range x).isSeparable.span.closure
  have : TopologicalSpace.SeparableSpace M := hsep.separableSpace
  have hmem : ∀ n, x n ∈ M := fun n =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  let y : ℕ → M := fun n => ⟨x n, hmem n⟩
  let u : ℕ → WeakDual ℝ M := fun n => StrongDual.toWeakDual (innerSL ℝ (y n))
  have hu : ∀ n, u n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ M) C := by
    intro n
    change dist (innerSL ℝ (y n)) 0 ≤ C
    rw [dist_zero_right, innerSL_apply_norm]
    exact hC n
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ M 0 C hu
  refine ⟨φ, hφ, ((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual a) : H), ?_⟩
  intro v
  have h1 : ∀ n, inner ℝ ((x ∘ φ) n) v = (u (φ n)) (M.orthogonalProjectionOnto v) := by
    intro n
    simp only [Function.comp, u]
    rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (y (φ n)) v]
    rfl
  have h2 : inner ℝ (((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual a) : M) : H) v
      = a (M.orthogonalProjectionOnto v) := by
    rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, InnerProductSpace.toDual_symm_apply]
    rfl
  simp_rw [h1, h2]
  exact ((WeakDual.eval_continuous (M.orthogonalProjectionOnto v)).tendsto a).comp hlim

/-- K2. Weak limits are unique. -/
theorem wlim_unique {x : ℕ → H} {p q : H} (hp : WLim x p) (hq : WLim x q) : p = q := by
  have h : inner ℝ p (p - q) = inner ℝ q (p - q) := tendsto_nhds_unique (hp (p - q)) (hq (p - q))
  have h2 : inner ℝ (p - q) (p - q) = 0 := by rw [inner_sub_left, h, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h2)


/-- K2'. A weak limit of a subsequence is a weak limit of further subsequences. -/
theorem wlim_comp {x : ℕ → H} {p : H} (hp : WLim x p) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WLim (x ∘ φ) p := fun v => (hp v).comp hφ.tendsto_atTop

private theorem aux_cluster_unique {x : ℕ → H} {p q : H}
    (hp : ∃ r : ℝ, Tendsto (fun n => ‖x n - p‖) atTop (𝓝 r))
    (hq : ∃ r : ℝ, Tendsto (fun n => ‖x n - q‖) atTop (𝓝 r))
    {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (h1 : WLim (x ∘ φ) p) (h2 : WLim (x ∘ ψ) q) : p = q := by
  obtain ⟨rp, hrp⟩ := hp
  obtain ⟨rq, hrq⟩ := hq
  have hid : ∀ n, inner ℝ (x n) (q - p)
      = ((‖x n - p‖ ^ 2 - ‖x n - q‖ ^ 2) - ‖p‖ ^ 2 + ‖q‖ ^ 2) / 2 := by
    intro n
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
    ring
  have hg : Tendsto (fun n => inner ℝ (x n) (q - p)) atTop
      (𝓝 (((rp ^ 2 - rq ^ 2) - ‖p‖ ^ 2 + ‖q‖ ^ 2) / 2)) := by
    simp_rw [hid]
    exact ((((hrp.pow 2).sub (hrq.pow 2)).sub_const _).add_const _).div_const _
  have e1 := tendsto_nhds_unique (hg.comp hφ.tendsto_atTop) (h1 (q - p))
  have e2 := tendsto_nhds_unique (hg.comp hψ.tendsto_atTop) (h2 (q - p))
  have h0 : inner ℝ (q - p) (q - p) = 0 := by rw [inner_sub_left, ← e1, ← e2, sub_self]
  exact (sub_eq_zero.mp (inner_self_eq_zero.mp h0)).symm

/-- K3. Opial's lemma. If `‖x n - z‖` converges for every `z ∈ S` and every weak sequential
cluster point of `x` lies in `S`, then `x` converges weakly to a point of `S`. -/
theorem opial [CompleteSpace H] (S : Set H) (hS : S.Nonempty) (x : ℕ → H)
    (hfej : ∀ z ∈ S, ∃ r : ℝ, Tendsto (fun n => ‖x n - z‖) atTop (𝓝 r))
    (hclu : ∀ (φ : ℕ → ℕ) (p : H), StrictMono φ → WLim (x ∘ φ) p → p ∈ S) :
    ∃ p ∈ S, WLim x p := by
  obtain ⟨z0, hz0⟩ := hS
  obtain ⟨r0, hr0⟩ := hfej z0 hz0
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hr0)
  have hbd : ∀ n, ‖x n‖ ≤ B + ‖z0‖ := by
    intro n
    have h := hB _ ⟨n, rfl⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)] at h
    calc ‖x n‖ = ‖(x n - z0) + z0‖ := by rw [sub_add_cancel]
      _ ≤ ‖x n - z0‖ + ‖z0‖ := norm_add_le _ _
      _ ≤ B + ‖z0‖ := by linarith
  obtain ⟨φ, hφ, p, hp⟩ := exists_wlim_subseq x _ hbd
  have hpS := hclu φ p hφ hp
  refine ⟨p, hpS, fun v => ?_⟩
  by_contra hne
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hne
  obtain ⟨ψ, hψ, hout⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨χ, hχ, q, hq⟩ := exists_wlim_subseq (x ∘ ψ) _ (fun n => hbd (ψ n))
  have hqS := hclu (ψ ∘ χ) q (hψ.comp hχ) hq
  have hpq : p = q := aux_cluster_unique (hfej p hpS) (hfej q hqS) hφ (hψ.comp hχ) hp hq
  have ht := hq v
  rw [← hpq] at ht
  obtain ⟨n, hn⟩ := (ht.eventually hs).exists
  exact hout (χ n) hn

/-- Monotone set-valued operator, as a relation. -/
def Mono (T : H → Set H) : Prop :=
  ∀ x y u v, u ∈ T x → v ∈ T y → 0 ≤ inner ℝ (x - y) (u - v)

/-- Maximal monotone, in the "no proper monotone extension" form the missions use. -/
def MaxMono (T : H → Set H) : Prop :=
  Mono T ∧ ∀ T' : H → Set H, Mono T' → (∀ x, T x ⊆ T' x) → T' = T

/-- K4a. A point monotonically related to the graph of a maximal monotone operator is in it. -/
theorem MaxMono.mem_of_related {T : H → Set H} (hT : MaxMono T) {x u : H}
    (h : ∀ y v, v ∈ T y → 0 ≤ inner ℝ (x - y) (u - v)) : u ∈ T x := by
  let T' : H → Set H := fun z => {w | w ∈ T z ∨ (z = x ∧ w = u)}
  have hmono : Mono T' := by
    intro a b c d hc hd
    rcases hc with hc | ⟨rfl, rfl⟩ <;> rcases hd with hd | ⟨rfl, rfl⟩
    · exact hT.1 _ _ _ _ hc hd
    · have := h a c hc
      have e : inner ℝ (a - b) (c - d) = inner ℝ (b - a) (d - c) := by
        rw [← neg_sub b a, ← neg_sub d c, inner_neg_neg]
      rw [e]; exact this
    · exact h b d hd
    · simp
  have hsub : ∀ z, T z ⊆ T' z := fun z w hw => Or.inl hw
  have hEq := hT.2 T' hmono hsub
  have : u ∈ T' x := Or.inr ⟨rfl, rfl⟩
  rw [hEq] at this
  exact this


private theorem aux_bdd_of_wlim [CompleteSpace H] {x : ℕ → H} {p : H} (hx : WLim x p) :
    ∃ C, ∀ n, ‖x n‖ ≤ C := by
  have hpt : ∀ v : H, ∃ C, ∀ n, ‖(innerSL ℝ (x n)) v‖ ≤ C := by
    intro v
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (hx v))
    exact ⟨C, fun n => by rw [innerSL_apply_apply]; exact hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpt
  exact ⟨C, fun n => by rw [← innerSL_apply_norm ℝ (x n)]; exact hC n⟩

/-- K4b under `CompleteSpace H` (the frozen K4b omits it; see KIT.md). -/
theorem aux_demiclosed_of_complete [CompleteSpace H] {T : H → Set H} (hT : MaxMono T)
    {x u : ℕ → H} {p q : H}
    (hmem : ∀ n, u n ∈ T (x n)) (hx : WLim x p) (hu : Tendsto u atTop (𝓝 q)) : q ∈ T p := by
  obtain ⟨C, hC⟩ := aux_bdd_of_wlim hx
  apply hT.mem_of_related
  intro y v hv
  have key : ∀ n, inner ℝ (x n - y) (u n - v)
      = (inner ℝ (x n) (q - v) - inner ℝ y (q - v)) + inner ℝ (x n - y) (u n - q) := by
    intro n
    rw [← inner_sub_left, ← inner_add_right]; congr 1; abel
  have h1 : Tendsto (fun n => inner ℝ (x n) (q - v) - inner ℝ y (q - v)) atTop
      (𝓝 (inner ℝ p (q - v) - inner ℝ y (q - v))) := (hx (q - v)).sub tendsto_const_nhds
  have h2 : Tendsto (fun n => inner ℝ (x n - y) (u n - q)) atTop (𝓝 0) := by
    have hq : Tendsto (fun n => (C + ‖y‖) * ‖u n - q‖) atTop (𝓝 0) := by
      have : Tendsto (fun n => ‖u n - q‖) atTop (𝓝 0) := by
        have := (hu.sub_const q).norm
        simpa using this
      simpa using this.const_mul (C + ‖y‖)
    refine squeeze_zero_norm (fun n => ?_) hq
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    exact (norm_sub_le _ _).trans (by linarith [hC n])
  have hlim := h1.add h2
  rw [add_zero, ← inner_sub_left] at hlim
  have hlim' : Tendsto (fun n => inner ℝ (x n - y) (u n - v)) atTop
      (𝓝 (inner ℝ (p - y) (q - v))) := by
    simp_rw [key]; exact hlim
  exact ge_of_tendsto' hlim' (fun n => hT.1 _ _ _ _ (hmem n) hv)

/-- K4b. Demiclosedness: the graph of a maximal monotone operator is weak × strong
sequentially closed (in a Hilbert space; false without completeness). -/
theorem MaxMono.demiclosed [CompleteSpace H] {T : H → Set H} (hT : MaxMono T) {x u : ℕ → H} {p q : H}
    (hmem : ∀ n, u n ∈ T (x n)) (hx : WLim x p) (hu : Tendsto u atTop (𝓝 q)) : q ∈ T p :=
  aux_demiclosed_of_complete hT hmem hx hu

private theorem aux_mem_of_related_surj {T : H → Set H} {μ : ℝ} (hμ : 0 < μ)
    (hsurj : ∀ z : H, ∃ x u, u ∈ T x ∧ z = x + μ • u) {x u : H}
    (h : ∀ y v, v ∈ T y → 0 ≤ inner ℝ (x - y) (u - v)) : u ∈ T x := by
  obtain ⟨y, w, hw, hz⟩ := hsurj (x + μ • u)
  have hxy : x - y = μ • (w - u) := by
    rw [smul_sub]
    calc x - y = (x + μ • u) - y - μ • u := by abel
      _ = (y + μ • w) - y - μ • u := by rw [hz]
      _ = μ • w - μ • u := by abel
  have h0 := h y w hw
  rw [hxy, inner_smul_left, ← neg_sub w u, inner_neg_right, real_inner_self_eq_norm_sq] at h0
  simp only [RCLike.conj_to_real] at h0
  have hn : ‖w - u‖ ^ 2 ≤ 0 := by nlinarith
  have hwu : w - u = 0 := by
    have : ‖w - u‖ = 0 := by nlinarith [norm_nonneg (w - u)]
    exact norm_eq_zero.mp this
  have hwu' : w = u := sub_eq_zero.mp hwu
  have hxy' : x = y := by rw [← sub_eq_zero, hxy, hwu, smul_zero]
  rw [hxy', ← hwu']; exact hw

/-- K5. Easy direction of Minty: a monotone operator with `range (I + μT) = H` for one `μ > 0`
is maximal monotone. -/
theorem maxMono_of_surj {T : H → Set H} (hT : Mono T) {μ : ℝ} (hμ : 0 < μ)
    (hsurj : ∀ z : H, ∃ x u, u ∈ T x ∧ z = x + μ • u) : MaxMono T := by
  refine ⟨hT, fun T' hT' hsub => ?_⟩
  funext z
  apply Set.Subset.antisymm _ (hsub z)
  intro w hw
  exact aux_mem_of_related_surj hμ hsurj
    (fun y v hv => hT' _ _ _ _ hw (hsub y hv))


private theorem aux_le_of_sq_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ a * b) :
    a ≤ b := by nlinarith

private theorem aux_resolvent_nonexp {A : H → Set H} (hA : Mono A) {J : H → H} {μ : ℝ}
    (hμ : 0 < μ) (hJ : ∀ z, μ⁻¹ • (z - J z) ∈ A (J z)) (w1 w2 : H) :
    ‖J w1 - J w2‖ ≤ ‖w1 - w2‖ := by
  have h := hA _ _ _ _ (hJ w1) (hJ w2)
  have e : μ⁻¹ • (w1 - J w1) - μ⁻¹ • (w2 - J w2) = μ⁻¹ • ((w1 - w2) - (J w1 - J w2)) := by
    rw [← smul_sub]; congr 1; abel
  rw [e, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq] at h
  have hμ' : 0 < μ⁻¹ := inv_pos.mpr hμ
  have h' : 0 ≤ inner ℝ (J w1 - J w2) (w1 - w2) - ‖J w1 - J w2‖ ^ 2 :=
    nonneg_of_mul_nonneg_right (by linarith) hμ'
  have hc := real_inner_le_norm (J w1 - J w2) (w1 - w2)
  exact aux_le_of_sq_le (norm_nonneg _) (norm_nonneg _) (by linarith)

/-- K6. If `A` is maximal monotone with resolvents `J γ` (in the missions' `IsResolvent` form) and
`B` is monotone and `L`-Lipschitz, then `A + B` is maximal monotone. -/
theorem maxMono_add_lipschitz [CompleteSpace H] {A : H → Set H} (hA : MaxMono A)
    (J : ℝ → H → H) (hJ : ∀ γ : ℝ, 0 < γ → ∀ z, γ⁻¹ • (z - J γ z) ∈ A (J γ z))
    {B : H → H} (hBm : ∀ x y, 0 ≤ inner ℝ (x - y) (B x - B y))
    {L : ℝ} (hL : 0 < L) (hBL : ∀ x y, ‖B x - B y‖ ≤ L * ‖x - y‖) :
    MaxMono (fun x => {w | ∃ a ∈ A x, w = a + B x}) := by
  have hmono : Mono (fun x => {w | ∃ a ∈ A x, w = a + B x}) := by
    rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    have e : a + B x - (b + B y) = (a - b) + (B x - B y) := by abel
    rw [e, inner_add_right]
    exact add_nonneg (hA.1 _ _ _ _ ha hb) (hBm x y)
  set μ : ℝ := (2 * L)⁻¹ with hμdef
  have hμ : 0 < μ := by positivity
  have hμL : μ * L = 1 / 2 := by rw [hμdef]; field_simp
  refine maxMono_of_surj hmono hμ ?_
  intro z
  let F : H → H := fun y => J μ (z - μ • B y)
  have hF : ContractingWith (1 / 2 : NNReal) F := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun y1 y2 => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    refine (aux_resolvent_nonexp hA.1 hμ (hJ μ hμ) _ _).trans ?_
    have e : z - μ • B y1 - (z - μ • B y2) = -(μ • (B y1 - B y2)) := by
      rw [smul_sub]; abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hμ.le]
    have := hBL y1 y2
    have h2 : μ * ‖B y1 - B y2‖ ≤ μ * (L * ‖y1 - y2‖) := mul_le_mul_of_nonneg_left this hμ.le
    calc μ * ‖B y1 - B y2‖ ≤ μ * (L * ‖y1 - y2‖) := h2
      _ = (μ * L) * ‖y1 - y2‖ := by ring
      _ = ((1 / 2 : NNReal) : ℝ) * ‖y1 - y2‖ := by rw [hμL]; norm_num
  set y := ContractingWith.fixedPoint F hF
  have hy : F y = y := ContractingWith.fixedPoint_isFixedPt (f := F) hF
  set w := z - μ • B y
  refine ⟨y, μ⁻¹ • (w - J μ w) + B y, ⟨μ⁻¹ • (w - J μ w), ?_, rfl⟩, ?_⟩
  · have := hJ μ hμ w
    have hFy : J μ w = y := hy
    rw [hFy] at this ⊢
    exact this
  · have hFy : J μ w = y := hy
    rw [hFy, smul_add, smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
    simp only [w]; abel

end OpialKit

namespace RRAux_ProjReflGrad_Weak_theorem_3_2

open Filter Topology ProjReflGrad.Weak

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma proj_spec [CompleteSpace H] (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C)
    (hne : C.Nonempty) (w : H) :
    proj C w ∈ C ∧ ∀ q ∈ C, inner ℝ (w - proj C w) (q - proj C w) ≤ 0 := by
  obtain ⟨v, hvC, hv⟩ := exists_norm_eq_iInf_of_complete_convex hne hCcl.isComplete hCcv w
  have hex : ∃ p, IsProj C w p := by
    refine ⟨v, hvC, fun q hq => ?_⟩
    rw [hv]
    exact ciInf_le ⟨0, by rintro _ ⟨r, rfl⟩; exact norm_nonneg _⟩ (⟨q, hq⟩ : C)
  have hp : proj C w = hex.choose := by
    unfold proj
    rw [dif_pos hex]
  rw [hp]
  obtain ⟨hpC, hpmin⟩ := hex.choose_spec
  refine ⟨hpC, ?_⟩
  have : ‖w - hex.choose‖ = ⨅ q : C, ‖w - q‖ := by
    apply le_antisymm
    · have : Nonempty C := ⟨⟨_, hpC⟩⟩
      exact le_ciInf (fun q => hpmin q q.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨r, rfl⟩; exact norm_nonneg _⟩ (⟨_, hpC⟩ : C)
  exact (norm_eq_iInf_iff_real_inner_le_zero hCcv hpC).mp this

lemma vi_step1 (X X1 Z A : H) (lam : ℝ) (h : inner ℝ ((X - lam • A) - X1) (Z - X1) ≤ 0) :
    ‖X1 - Z‖ ^ 2 ≤ ‖X - Z‖ ^ 2 - ‖X - X1‖ ^ 2 - 2 * lam * inner ℝ A (X1 - Z) := by
  have e : X - Z = (X - X1) + (X1 - Z) := by abel
  have e2 : (X - lam • A) - X1 = (X - X1) - lam • A := by abel
  have e3 : Z - X1 = -(X1 - Z) := by abel
  rw [e, norm_add_sq_real]
  rw [e2, e3, inner_neg_right, inner_sub_left, real_inner_smul_left] at h
  linarith

lemma vi_step2 (Xm Xn X1 Yn B : H) (lam : ℝ) (hy : Yn = (2 : ℝ) • Xn - Xm)
    (h1 : inner ℝ ((Xm - lam • B) - Xn) (X1 - Xn) ≤ 0)
    (h2 : inner ℝ ((Xm - lam • B) - Xn) (Xm - Xn) ≤ 0) :
    2 * lam * inner ℝ B (Yn - X1) ≤ ‖X1 - Xn‖ ^ 2 - ‖Yn - Xn‖ ^ 2 - ‖X1 - Yn‖ ^ 2 := by
  have hs := add_nonpos h1 h2
  rw [← inner_add_right] at hs
  have e1 : (X1 - Xn) + (Xm - Xn) = X1 - Yn := by rw [hy]; module
  have e2 : (Xm - lam • B) - Xn = (Xn - Yn) - lam • B := by rw [hy]; module
  rw [e1, e2, inner_sub_left, real_inner_smul_left] at hs
  have e3 : X1 - Xn = (X1 - Yn) - (Xn - Yn) := by abel
  have e4 : Yn - X1 = -(X1 - Yn) := by abel
  rw [e3, norm_sub_sq_real, e4, inner_neg_right, norm_sub_rev Yn Xn]
  have c1 := real_inner_comm (X1 - Yn) (Xn - Yn)
  have c2 := real_inner_comm B (X1 - Yn)
  nlinarith

lemma amgm (θ a b c s : ℝ) (hs : s * s = 2) (hs1 : 1 ≤ s) (hθ : 0 ≤ θ) :
    2 * θ * (a + b) * c ≤ θ * a ^ 2 + θ * c ^ 2 + θ * (1 + s) * b ^ 2 + θ * (s - 1) * c ^ 2 := by
  have h1 := mul_nonneg hθ (sq_nonneg (a - c))
  have h2 := mul_nonneg (mul_nonneg hθ (sub_nonneg.mpr hs1)) (sq_nonneg ((1 + s) * b - c))
  have e : θ * (s - 1) * ((1 + s) * b - c) ^ 2
      = θ * ((1 + s) * b ^ 2 - 2 * b * c + (s - 1) * c ^ 2) := by
    have : (s - 1) * (1 + s) = 1 := by nlinarith
    linear_combination (θ * b ^ 2 * (1 + s)) * this - θ * 2 * b * c * this + 0 * hs
  nlinarith [e]

/-- One step of the Lyapunov inequality (Malitsky 2015, proof of Thm 3.2), monotone case,
keeping the `e‖x_{n+1} - x_n‖²` term. -/
lemma one_step [CompleteSpace H] (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C)
    (hne : C.Nonempty) (F : H → H) (L lam : ℝ)
    (hC2 : IsMonotoneMap F)
    (hL : 0 < L) (hC3 : IsLipschitzMap F L) (hlam0 : 0 < lam)
    (z : H) (Xm Xn X1 Yn Ym : H) (hXm : Xm ∈ C) (hz : z ∈ C) (hy : Yn = (2 : ℝ) • Xn - Xm)
    (hXn : Xn = proj C (Xm - lam • F Ym))
    (hX1 : X1 = proj C (Xn - lam • F Yn)) :
    ‖X1 - z‖ ^ 2 + lam * L * ‖X1 - Yn‖ ^ 2 + 2 * lam * inner ℝ (F z) (Xn - z)
      + (1 - lam * L * (1 + Real.sqrt 2)) * ‖X1 - Yn‖ ^ 2
      + (1 - lam * L * (1 + Real.sqrt 2)) * ‖Yn - Xn‖ ^ 2
      + 2 * lam * inner ℝ (F z) (Xn - z)
      ≤ ‖Xn - z‖ ^ 2 + lam * L * ‖Xn - Ym‖ ^ 2 + 2 * lam * inner ℝ (F z) (Xm - z) := by
  obtain ⟨hX1C, hX1vi⟩ := proj_spec C hCcl hCcv hne (Xn - lam • F Yn)
  obtain ⟨hXnC, hXnvi⟩ := proj_spec C hCcl hCcv hne (Xm - lam • F Ym)
  rw [← hX1] at hX1C hX1vi
  rw [← hXn] at hXnC hXnvi
  have E1 := vi_step1 Xn X1 z (F Yn) lam (hX1vi z hz)
  have E2 := vi_step2 Xm Xn X1 Yn (F Ym) lam hy (hXnvi X1 hX1C) (hXnvi Xm hXm)
  set s := Real.sqrt 2 with hsdef
  have hs : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr (by norm_num)
  have E3 : inner ℝ (F Yn - F Ym) (Yn - X1) ≤ L * (‖Yn - Xn‖ + ‖Xn - Ym‖) * ‖X1 - Yn‖ := by
    have h1 := real_inner_le_norm (F Yn - F Ym) (Yn - X1)
    have h2 := hC3 Yn Ym
    have h3 : ‖Yn - Ym‖ ≤ ‖Yn - Xn‖ + ‖Xn - Ym‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev Yn X1] at h1
    have h4 : L * ‖Yn - Ym‖ ≤ L * (‖Yn - Xn‖ + ‖Xn - Ym‖) := mul_le_mul_of_nonneg_left h3 hL.le
    have h5 := mul_le_mul_of_nonneg_right (h2.trans h4) (norm_nonneg (X1 - Yn))
    linarith
  have E4 := hC2 Yn z
  have E5 : inner ℝ (F z) (Yn - z) = 2 * inner ℝ (F z) (Xn - z) - inner ℝ (F z) (Xm - z) := by
    have : Yn - z = (2 : ℝ) • (Xn - z) - (Xm - z) := by rw [hy]; module
    rw [this, inner_sub_right, real_inner_smul_right]
  have E6 : inner ℝ (F Yn) (X1 - z) = inner ℝ (F Yn - F z) (Yn - z) + inner ℝ (F z) (Yn - z)
      - inner ℝ (F Yn - F Ym) (Yn - X1) - inner ℝ (F Ym) (Yn - X1) := by
    have : X1 - z = (Yn - z) - (Yn - X1) := by abel
    rw [this, inner_sub_right, inner_sub_left, inner_sub_left]; ring
  have E7 := amgm (lam * L) ‖Xn - Ym‖ ‖Yn - Xn‖ ‖X1 - Yn‖ s hs hs1 (by positivity)
  have hl2 : 0 ≤ 2 * lam := by positivity
  have F3 := mul_le_mul_of_nonneg_left E3 hl2
  have F4 := mul_nonneg hl2 E4
  have F5 := congrArg (fun t => 2 * lam * t) E5
  have F6 := congrArg (fun t => 2 * lam * t) E6
  rw [norm_sub_rev Xn X1] at E1
  linarith [E1, E2, F3, F4, F5, F6, E7]

lemma desc (u c : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) (hc : ∀ k, 0 ≤ c k)
    (h : ∀ k, u (k + 1) + c k ≤ u k) :
    (∃ r, Tendsto u atTop (𝓝 r)) ∧ Tendsto c atTop (𝓝 0) := by
  have hanti : Antitone u := antitone_nat_of_succ_le (fun k => by linarith [hc k, h k])
  have hb : BddBelow (Set.range u) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hu k⟩
  have ht := tendsto_atTop_ciInf hanti hb
  refine ⟨⟨_, ht⟩, ?_⟩
  have h2 : Tendsto (fun k => u k - u (k + 1)) atTop (𝓝 ((⨅ i, u i) - ⨅ i, u i)) :=
    ht.sub (ht.comp (tendsto_add_atTop_nat 1))
  rw [sub_self] at h2
  exact squeeze_zero hc (fun k => by linarith [h k]) h2

omit [InnerProductSpace ℝ H] in
lemma sq_to_norm (v : ℕ → H) (h : Tendsto (fun n => ‖v n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ‖v n‖) atTop (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  refine this.congr (fun n => ?_)
  simp [Real.sqrt_sq (norm_nonneg (v n))]

lemma fejer [CompleteSpace H] (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C)
    (F : H → H) (L lam : ℝ) (hC2 : IsMonotoneMap F) (hL : 0 < L) (hC3 : IsLipschitzMap F L)
    (hlam0 : 0 < lam) (hθ1 : lam * L * (1 + Real.sqrt 2) < 1)
    (x y : ℕ → H) (hrun : IsPRGRun C F lam x y) (z : H) (hz : z ∈ solSet C F) :
    (∃ r, Tendsto (fun n => ‖x n - z‖) atTop (𝓝 r)) ∧
      Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖x (n + 1) - y n‖) atTop (𝓝 0) := by
  have hzC : z ∈ C := hz.1
  have hne : C.Nonempty := ⟨z, hzC⟩
  have hxC : ∀ k, x (k + 1) ∈ C := by
    intro k
    rw [(hrun.2 k).1]
    exact (proj_spec C hCcl hCcv hne _).1
  have hg : ∀ k, 0 ≤ inner ℝ (F z) (x (k + 1) - z) := fun k => hz.2 _ (hxC k)
  set e := 1 - lam * L * (1 + Real.sqrt 2) with he
  have hepos : 0 < e := by linarith
  have hθ0 : 0 ≤ lam * L := by positivity
  let P : ℕ → ℝ := fun k => ‖x (k + 2) - z‖ ^ 2 + lam * L * ‖x (k + 2) - y (k + 1)‖ ^ 2
    + 2 * lam * inner ℝ (F z) (x (k + 1) - z)
  let c : ℕ → ℝ := fun k => e * ‖x (k + 3) - y (k + 2)‖ ^ 2 + e * ‖y (k + 2) - x (k + 2)‖ ^ 2
    + 2 * lam * inner ℝ (F z) (x (k + 2) - z)
  have hP0 : ∀ k, 0 ≤ P k := by
    intro k
    have := hg k
    have : 0 ≤ lam * L * ‖x (k + 2) - y (k + 1)‖ ^ 2 := by positivity
    have : 0 ≤ 2 * lam * inner ℝ (F z) (x (k + 1) - z) := by positivity
    simp only [P]; positivity
  have hc0 : ∀ k, 0 ≤ c k := by
    intro k
    have := hg (k + 1)
    have : 0 ≤ 2 * lam * inner ℝ (F z) (x (k + 2) - z) := by positivity
    simp only [c]; positivity
  have hrec : ∀ k, P (k + 1) + c k ≤ P k := by
    intro k
    have hstep := one_step C hCcl hCcv hne F L lam hC2 hL hC3 hlam0 z (x (k + 1)) (x (k + 2))
      (x (k + 3)) (y (k + 2)) (y (k + 1)) (hxC k) hzC (hrun.2 (k + 1)).2 (hrun.2 (k + 1)).1
      (hrun.2 (k + 2)).1
    simp only [P, c]
    rw [← he] at hstep
    linarith
  obtain ⟨⟨R, hR⟩, hc⟩ := desc P c hP0 hc0 hrec
  -- the three components of `c` tend to zero
  have hA : Tendsto (fun k => ‖x (k + 3) - y (k + 2)‖ ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => c k / e) atTop (𝓝 0) := by simpa using hc.div_const e
    refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) h1
    rw [le_div_iff₀ hepos]
    have := hg (k + 1)
    have : 0 ≤ 2 * lam * inner ℝ (F z) (x (k + 2) - z) := by positivity
    have : 0 ≤ e * ‖y (k + 2) - x (k + 2)‖ ^ 2 := by positivity
    simp only [c]; linarith
  have hB : Tendsto (fun k => ‖y (k + 2) - x (k + 2)‖ ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => c k / e) atTop (𝓝 0) := by simpa using hc.div_const e
    refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) h1
    rw [le_div_iff₀ hepos]
    have := hg (k + 1)
    have : 0 ≤ 2 * lam * inner ℝ (F z) (x (k + 2) - z) := by positivity
    have : 0 ≤ e * ‖x (k + 3) - y (k + 2)‖ ^ 2 := by positivity
    simp only [c]; linarith
  have hG : Tendsto (fun k => inner ℝ (F z) (x (k + 2) - z)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => c k / (2 * lam)) atTop (𝓝 0) := by simpa using hc.div_const (2 * lam)
    refine squeeze_zero (fun k => hg (k + 1)) (fun k => ?_) h1
    rw [le_div_iff₀ (by positivity)]
    have : 0 ≤ e * ‖x (k + 3) - y (k + 2)‖ ^ 2 := by positivity
    have : 0 ≤ e * ‖y (k + 2) - x (k + 2)‖ ^ 2 := by positivity
    simp only [c]; linarith
  -- shifted versions
  have hA' : Tendsto (fun k => ‖x (k + 2) - y (k + 1)‖ ^ 2) atTop (𝓝 0) := by
    exact (tendsto_add_atTop_iff_nat (f := fun k => ‖x (k + 2) - y (k + 1)‖ ^ 2) 1).mp hA
  have hG' : Tendsto (fun k => inner ℝ (F z) (x (k + 1) - z)) atTop (𝓝 0) := by
    exact (tendsto_add_atTop_iff_nat 1).mp hG
  have hN2 : Tendsto (fun k => ‖x (k + 2) - z‖ ^ 2) atTop (𝓝 R) := by
    have := (hR.sub ((hA'.const_mul (lam * L)))).sub (hG'.const_mul (2 * lam))
    simp only [mul_zero, sub_zero] at this
    refine this.congr (fun k => ?_)
    simp only [P]; ring
  refine ⟨⟨Real.sqrt R, ?_⟩, ?_, ?_⟩
  · have := (Real.continuous_sqrt.tendsto R).comp hN2
    have h2 : Tendsto (fun k => ‖x (k + 2) - z‖) atTop (𝓝 (Real.sqrt R)) :=
      this.congr (fun k => by simp [Real.sqrt_sq (norm_nonneg _)])
    exact (tendsto_add_atTop_iff_nat 2).mp h2
  · have hB2 : Tendsto (fun k => ‖x (k + 2) - x (k + 1)‖ ^ 2) atTop (𝓝 0) := by
      refine hB.congr (fun k => ?_)
      congr 2
      rw [(hrun.2 (k + 1)).2]; module
    have := sq_to_norm (fun k => x (k + 2) - x (k + 1)) hB2
    exact (tendsto_add_atTop_iff_nat 1).mp this
  · have := sq_to_norm (fun k => x (k + 2) - y (k + 1)) hA'
    exact (tendsto_add_atTop_iff_nat 1).mp this

lemma wclosed [CompleteSpace H] (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C)
    (hne : C.Nonempty) (u : ℕ → H) (hu : ∀ n, u n ∈ C) (p : H) (hw : OpialKit.WLim u p) :
    p ∈ C := by
  obtain ⟨hqC, hq⟩ := proj_spec C hCcl hCcv hne p
  set q := proj C p
  have h1 : ∀ n, inner ℝ (u n) (p - q) ≤ inner ℝ q (p - q) := by
    intro n
    have := hq (u n) (hu n)
    rw [real_inner_comm, inner_sub_left] at this
    linarith
  have h2 := le_of_tendsto' (hw (p - q)) h1
  have h3 : inner ℝ (p - q) (p - q) ≤ 0 := by rw [inner_sub_left]; linarith
  rw [real_inner_self_eq_norm_sq] at h3
  have h4 : ‖p - q‖ = 0 := by nlinarith [norm_nonneg (p - q)]
  rw [norm_eq_zero, sub_eq_zero] at h4
  rw [h4]; exact hqC

lemma minty (C : Set H) (hCcv : Convex ℝ C) (F : H → H) (hF : Continuous F) (p : H) (hp : p ∈ C)
    (h : ∀ c ∈ C, 0 ≤ inner ℝ (F c) (c - p)) : p ∈ solSet C F := by
  refine ⟨hp, fun w hw => ?_⟩
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht0 : ∀ n, 0 < t n := fun n => by positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n => by
    simp only [t]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmem : ∀ n, p + t n • (w - p) ∈ C := fun n =>
    hCcv.add_smul_sub_mem hp hw ⟨(ht0 n).le, ht1 n⟩
  have hineq : ∀ n, 0 ≤ inner ℝ (F (p + t n • (w - p))) (w - p) := by
    intro n
    have := h _ (hmem n)
    rw [add_sub_cancel_left, real_inner_smul_right] at this
    exact (mul_nonneg_iff_of_pos_left (ht0 n)).mp this
  have hlim : Tendsto (fun n => p + t n • (w - p)) atTop (𝓝 p) := by
    have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (w - p)
    have := (tendsto_const_nhds (x := p)).add h0
    rw [zero_smul, add_zero] at this
    exact this
  have hlim2 := ((hF.tendsto p).comp hlim).inner (𝕜 := ℝ) (tendsto_const_nhds (x := w - p))
  exact ge_of_tendsto' hlim2 hineq

lemma pt_ineq (F : H → H) (L lam : ℝ) (hC2 : IsMonotoneMap F) (hL : 0 < L)
    (hC3 : IsLipschitzMap F L) (hlam0 : 0 < lam) (c z0 Xn X1 Yn : H)
    (hproj : inner ℝ ((Xn - lam • F Yn) - X1) (c - X1) ≤ 0) :
    -(‖Xn - X1‖ * (‖c - z0‖ + ‖X1 - z0‖)
      + lam * (‖F z0‖ + L * (‖Yn - X1‖ + ‖X1 - z0‖)) * ‖X1 - Yn‖
      + lam * ‖F c‖ * ‖Yn - Xn‖) ≤ lam * inner ℝ (F c) (c - Xn) := by
  have m1 := hC2 c Yn
  rw [inner_sub_left] at m1
  have e1 : (Xn - lam • F Yn) - X1 = (Xn - X1) - lam • F Yn := by abel
  rw [e1, inner_sub_left, real_inner_smul_left] at hproj
  have e2 : inner ℝ (F Yn) (c - Yn) = inner ℝ (F Yn) (c - X1) + inner ℝ (F Yn) (X1 - Yn) := by
    rw [← inner_add_right]; congr 1; abel
  have e3 : inner ℝ (F c) (c - Xn) = inner ℝ (F c) (c - Yn) + inner ℝ (F c) (Yn - Xn) := by
    rw [← inner_add_right]; congr 1; abel
  -- bounds
  have b1 : -(‖Xn - X1‖ * (‖c - z0‖ + ‖X1 - z0‖)) ≤ inner ℝ (Xn - X1) (c - X1) := by
    have h := neg_abs_le (inner ℝ (Xn - X1) (c - X1))
    have h2 := abs_real_inner_le_norm (Xn - X1) (c - X1)
    have h3 : ‖c - X1‖ ≤ ‖c - z0‖ + ‖X1 - z0‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub c z0 X1
      rwa [norm_sub_rev z0 X1] at this
    have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg (Xn - X1))
    linarith
  have b2 : -((‖F z0‖ + L * (‖Yn - X1‖ + ‖X1 - z0‖)) * ‖X1 - Yn‖) ≤ inner ℝ (F Yn) (X1 - Yn) := by
    have h := neg_abs_le (inner ℝ (F Yn) (X1 - Yn))
    have h2 := abs_real_inner_le_norm (F Yn) (X1 - Yn)
    have h3 : ‖F Yn‖ ≤ ‖F z0‖ + L * (‖Yn - X1‖ + ‖X1 - z0‖) := by
      have a1 : ‖F Yn‖ ≤ ‖F z0‖ + ‖F Yn - F z0‖ := by
        have := norm_add_le (F z0) (F Yn - F z0); simpa using this
      have a2 := hC3 Yn z0
      have a3 : ‖Yn - z0‖ ≤ ‖Yn - X1‖ + ‖X1 - z0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      have a4 := mul_le_mul_of_nonneg_left a3 hL.le
      linarith
    have h4 := mul_le_mul_of_nonneg_right h3 (norm_nonneg (X1 - Yn))
    linarith
  have b3 : -(‖F c‖ * ‖Yn - Xn‖) ≤ inner ℝ (F c) (Yn - Xn) := by
    have h := neg_abs_le (inner ℝ (F c) (Yn - Xn))
    have h2 := abs_real_inner_le_norm (F c) (Yn - Xn)
    linarith
  have c2 := mul_le_mul_of_nonneg_left b2 hlam0.le
  have c3 := mul_le_mul_of_nonneg_left b3 hlam0.le
  have c4 := mul_le_mul_of_nonneg_left m1 hlam0.le
  rw [e3]
  rw [e2] at c4
  nlinarith [c2, c3, c4, b1, hproj]

end RRAux_ProjReflGrad_Weak_theorem_3_2

open ProjReflGrad.Weak in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L lam : ℝ)
    (hC1 : (solSet C F).Nonempty) (hC2 : IsMonotoneMap F) (hL : 0 < L) (hC3 : IsLipschitzMap F L)
    (hlam0 : 0 < lam) (hlam1 : lam < (Real.sqrt 2 - 1) / L)
    (x y : ℕ → H) (hrun : IsPRGRun C F lam x y) :
    ∃ xs ∈ solSet C F, IsWeakLimit x xs := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hθlt : lam * L < Real.sqrt 2 - 1 := by
    rw [lt_div_iff₀ hL] at hlam1; exact hlam1
  have hs1 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hθ1 : lam * L * (1 + Real.sqrt 2) < 1 := by nlinarith
  obtain ⟨z0, hz0⟩ := hC1
  have hne : C.Nonempty := ⟨z0, hz0.1⟩
  have hFej := fun z (hz : z ∈ solSet C F) =>
    RRAux_ProjReflGrad_Weak_theorem_3_2.fejer C hCcl hCcv F L lam hC2 hL hC3 hlam0 hθ1 x y hrun z hz
  obtain ⟨⟨r0, hr0⟩, hd, ha⟩ := hFej z0 hz0
  have hxC : ∀ k, x (k + 1) ∈ C := by
    intro k
    rw [(hrun.2 k).1]
    exact (RRAux_ProjReflGrad_Weak_theorem_3_2.proj_spec C hCcl hCcv hne _).1
  have hb : Filter.Tendsto (fun n => ‖y n - x n‖) Filter.atTop (nhds 0) := by
    refine (Filter.tendsto_add_atTop_iff_nat (f := fun n => ‖y n - x n‖) 1).mp ?_
    refine hd.congr (fun n => ?_)
    show ‖x (n + 1) - x n‖ = ‖y (n + 1) - x (n + 1)‖
    rw [(hrun.2 n).2]; congr 1; module
  have hFc : Continuous F := (LipschitzWith.of_dist_le' (K := L)
    (fun a b => by simpa [dist_eq_norm] using hC3 a b)).continuous
  have hd' : Filter.Tendsto (fun n => ‖x n - x (n + 1)‖) Filter.atTop (nhds 0) :=
    hd.congr (fun n => norm_sub_rev _ _)
  have ha' : Filter.Tendsto (fun n => ‖y n - x (n + 1)‖) Filter.atTop (nhds 0) :=
    ha.congr (fun n => norm_sub_rev _ _)
  have hr1 : Filter.Tendsto (fun n => ‖x (n + 1) - z0‖) Filter.atTop (nhds r0) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun n => ‖x n - z0‖) 1).mpr hr0
  have hmain := OpialKit.opial (solSet C F) ⟨z0, hz0⟩ x (fun z hz => (hFej z hz).1) ?_
  · exact hmain
  intro φ p hφ hw
  have hpC : p ∈ C := by
    refine RRAux_ProjReflGrad_Weak_theorem_3_2.wclosed C hCcl hCcv hne (fun n => x (φ (n + 1)))
      (fun n => ?_) p (fun v => ?_)
    · have := hφ.id_le (n + 1)
      obtain ⟨k, hk⟩ : ∃ k, φ (n + 1) = k + 1 := ⟨φ (n + 1) - 1, by simp at this; omega⟩
      simp only [hk]; exact hxC k
    · exact (Filter.tendsto_add_atTop_iff_nat (f := fun n => inner ℝ ((x ∘ φ) n) v) 1).mpr (hw v)
  refine RRAux_ProjReflGrad_Weak_theorem_3_2.minty C hCcv F hFc p hpC (fun c hc => ?_)
  let S : ℕ → ℝ := fun n => ‖x n - x (n + 1)‖ * (‖c - z0‖ + ‖x (n + 1) - z0‖)
      + lam * (‖F z0‖ + L * (‖y n - x (n + 1)‖ + ‖x (n + 1) - z0‖)) * ‖x (n + 1) - y n‖
      + lam * ‖F c‖ * ‖y n - x n‖
  have hS : Filter.Tendsto (fun n => -S n) Filter.atTop (nhds 0) := by
    have h1 := hd'.mul ((tendsto_const_nhds (x := ‖c - z0‖)).add hr1)
    have h2 := ((tendsto_const_nhds (x := lam)).mul ((tendsto_const_nhds (x := ‖F z0‖)).add
      ((tendsto_const_nhds (x := L)).mul (ha'.add hr1)))).mul ha
    have h3 := (tendsto_const_nhds (x := lam * ‖F c‖)).mul hb
    have := ((h1.add h2).add h3).neg
    simp only [mul_zero, zero_mul, add_zero, neg_zero] at this
    exact this
  have hineq : ∀ n, -S n ≤ lam * inner ℝ (F c) (c - x n) := by
    intro n
    have hp := (RRAux_ProjReflGrad_Weak_theorem_3_2.proj_spec C hCcl hCcv hne
      (x n - lam • F (y n))).2 c hc
    rw [← (hrun.2 n).1] at hp
    exact RRAux_ProjReflGrad_Weak_theorem_3_2.pt_ineq F L lam hC2 hL hC3 hlam0 c z0 (x n)
      (x (n + 1)) (y n) hp
  have hlim2 : Filter.Tendsto (fun n => lam * inner ℝ (F c) (c - x (φ n))) Filter.atTop
      (nhds (lam * inner ℝ (F c) (c - p))) := by
    have h := ((hw (F c)).const_sub (inner ℝ c (F c))).const_mul lam
    refine (h.congr (fun n => ?_)).trans ?_
    · simp only [Function.comp, inner_sub_right, real_inner_comm (F c)]
    · rw [inner_sub_right, real_inner_comm (F c) c, real_inner_comm (F c) p]
  have hle := le_of_tendsto_of_tendsto' (hS.comp hφ.tendsto_atTop) hlim2 (fun n => hineq (φ n))
  exact (mul_nonneg_iff_of_pos_left hlam0).mp hle

#print axioms solution
