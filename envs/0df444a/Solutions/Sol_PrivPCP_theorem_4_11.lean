-- Prove2me | solution 1 for PrivPCP.theorem_4_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:33:40.101155+00:00
-- url     : https://prove2.me/submissions/d38b7676-de08-4968-956a-284044268bfe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PrivPCP_gridQ
import Definitions.Def_PrivPCP_rsNested
import Definitions.Def_PrivPCP_NestedCodes
import Definitions.Def_PrivPCP_certLaw
import Definitions.Def_PrivPCP_PunctRSPE
import Theorems.Thm_PrivPCP_lemma_4_13_kpos


namespace PrivPCP.TDual

open GoodQLTC Classical

variable {F : Type} [Field F]

lemma mem_dualCode {α : Type} [Fintype α] (U : Submodule F (α → F)) (y : α → F) :
    y ∈ dualCode U ↔ ∀ x ∈ U, x ⬝ᵥ y = 0 := Iff.rfl

theorem dualCode_dualCode {α : Type} [Fintype α] (U : Submodule F (α → F)) :
    dualCode (dualCode U) = U := by
  ext v
  rw [mem_dualCode]
  constructor
  · intro h
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    set y : α → F := (dotProductEquiv F α).symm φ with hy
    have hφy : ∀ w, φ w = y ⬝ᵥ w := by
      intro w
      have : φ = dotProductEquiv F α y := by rw [hy, LinearEquiv.apply_symm_apply]
      rw [this]; rfl
    rw [hφy]
    have hyU : y ∈ dualCode U := by
      intro u hu
      rw [dotProduct_comm, ← hφy]
      exact (Submodule.mem_dualAnnihilator φ).1 hφ u hu
    exact h y hyU
  · intro hv y hy
    rw [dotProduct_comm]
    exact hy v hv

lemma dualCode_antitone {α : Type} [Fintype α] {U U' : Submodule F (α → F)} (h : U ≤ U') :
    dualCode U' ≤ dualCode U := fun y hy x hx => hy x (h hx)

theorem dualCode_iSup {α ι : Type} [Fintype α] (A : ι → Submodule F (α → F)) :
    dualCode (⨆ i, A i) = ⨅ i, dualCode (A i) := by
  apply le_antisymm
  · exact le_iInf fun i => dualCode_antitone (le_iSup A i)
  · intro y hy x hx
    rw [Submodule.mem_iInf] at hy
    refine Submodule.iSup_induction A (motive := fun x => x ⬝ᵥ y = 0) hx ?_ ?_ ?_
    · intro i x hx; exact hy i x hx
    · exact zero_dotProduct y
    · intro x x' h1 h2; rw [add_dotProduct, h1, h2, add_zero]

theorem dualCode_iInf {α ι : Type} [Fintype α] (A : ι → Submodule F (α → F)) :
    dualCode (⨅ i, A i) = ⨆ i, dualCode (A i) := by
  have : (⨅ i, A i) = dualCode (⨆ i, dualCode (A i)) := by
    rw [dualCode_iSup]; simp_rw [dualCode_dualCode]
  rw [this, dualCode_dualCode]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

lemma mem_axisCode_iff (C : ∀ i, Submodule F (S i → F)) (i : ι) (x : (∀ i, S i) → F) :
    x ∈ axisCode C i ↔ ∀ b : (∀ i, S i), (fun t => x (Function.update b i t)) ∈ C i := by
  simp only [axisCode, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.funLeft_apply]
  exact Iff.rfl

/-- sum over a line -/
lemma sum_fiber_line (i : ι) (t0 : S i) (b : ∀ i, S i) (hb : b i = t0) (f : (∀ i, S i) → F) :
    ∑ ω ∈ Finset.univ.filter (fun ω => Function.update ω i t0 = b), f ω =
      ∑ t, f (Function.update b i t) := by
  symm
  refine Finset.sum_nbij' (fun t => Function.update b i t) (fun ω => ω i) ?_ ?_ ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Function.update_idem, ← hb, Function.update_eq_self]
  · intro ω _; exact Finset.mem_univ _
  · intro t _; exact Function.update_self i t b
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rw [← hω, Function.update_idem, Function.update_eq_self]
  · intro t _; rfl

lemma sum_by_lines (i : ι) (t0 : S i) (f : (∀ i, S i) → F) :
    ∑ ω, f ω = ∑ b, ∑ ω ∈ Finset.univ.filter (fun ω => Function.update ω i t0 = b), f ω :=
  (Finset.sum_fiberwise Finset.univ _ f).symm

theorem dualCode_axisCode (C : ∀ i, Submodule F (S i → F)) (i : ι) :
    dualCode (axisCode C i) = axisCode (fun j => dualCode (C j)) i := by
  by_cases hS : IsEmpty (S i)
  · -- the grid is empty: both sides are everything
    have hΩ : IsEmpty (∀ i, S i) := ⟨fun ω => hS.false (ω i)⟩
    ext y
    constructor
    · intro _; rw [mem_axisCode_iff]; intro b; exact (hΩ.false b).elim
    · intro _ x _; simp [dotProduct, Finset.univ_eq_empty]
  rw [not_isEmpty_iff] at hS
  obtain ⟨t0⟩ := hS
  ext y
  rw [mem_axisCode_iff]
  constructor
  · intro hy b c hc
    -- place `c` on the line through `b`
    set b' := Function.update b i t0
    let P : (∀ i, S i) → F := fun ω => if Function.update ω i t0 = b' then c (ω i) else 0
    have hP : P ∈ axisCode C i := by
      rw [mem_axisCode_iff]
      intro b''
      have : (fun t => P (Function.update b'' i t)) =
          if Function.update b'' i t0 = b' then c else 0 := by
        funext t
        simp only [P, Function.update_idem, Function.update_self]
        split_ifs <;> rfl
      rw [this]; split_ifs
      · exact hc
      · exact (C i).zero_mem
    have h0 := hy P hP
    rw [dotProduct, sum_by_lines i t0] at h0
    rw [Finset.sum_eq_single b'] at h0
    · rw [sum_fiber_line i t0 b' (by simp [b'])] at h0
      simp only [P, Function.update_idem, Function.update_self, if_true] at h0
      rw [dotProduct]
      simpa [b', Function.update_idem] using h0
    · intro b0 _ hb0
      refine Finset.sum_eq_zero fun ω hω => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      simp [P, hω, hb0]
    · simp
  · intro hy x hx
    rw [mem_axisCode_iff] at hx
    rw [dotProduct, sum_by_lines i t0]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b i = t0
    · rw [sum_fiber_line i t0 b hb]
      exact hy b (fun t => x (Function.update b i t)) (hx b)
    · refine Finset.sum_eq_zero fun ω hω => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      exact absurd (by rw [← hω, Function.update_self]) hb

theorem dualCode_tensorCode (V : ∀ i, Submodule F (S i → F)) :
    dualCode (tensorCode V) = ⨆ i, axisCode (fun j => dualCode (V j)) i := by
  unfold tensorCode
  rw [dualCode_iInf]
  simp_rw [dualCode_axisCode]

end PrivPCP.TDual


namespace PrivPCP.RSD

open GoodQLTC Classical PrivPCP.TDual Polynomial

variable {F : Type} [Field F] [Fintype F]

/-- power sums over a finite multiplicative subgroup vanish -/
lemma powsum (Ω : Finset F) (hmul : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y ∈ Ω) (h0 : (0 : F) ∉ Ω)
    (j : ℕ) (hj0 : 0 < j) (hj : j < Ω.card) : ∑ x ∈ Ω, x ^ j = 0 := by
  -- some element with `y ^ j ≠ 1`
  obtain ⟨y, hy, hyj⟩ : ∃ y ∈ Ω, y ^ j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hne : (X ^ j - 1 : F[X]) ≠ 0 := by
      have := X_pow_sub_C_ne_zero hj0 (1 : F); simpa using this
    have hroots : Ω ⊆ ((X ^ j - 1 : F[X]).roots).toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hne]
      simp [hcon x hx]
    have h1 := Finset.card_le_card hroots
    have h2 := Multiset.toFinset_card_le ((X ^ j - 1 : F[X]).roots)
    have h3 := card_roots' (X ^ j - 1 : F[X])
    have h4 : (X ^ j - 1 : F[X]).natDegree = j := by
      rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hj0]
    omega
  have hperm : ∑ x ∈ Ω, (y * x) ^ j = ∑ x ∈ Ω, x ^ j := by
    apply Finset.sum_nbij (fun x => y * x)
    · intro x hx; exact hmul y hy x hx
    · intro x _ x' _ h
      have hy0 : y ≠ 0 := fun e => h0 (e ▸ hy)
      exact mul_left_cancel₀ hy0 h
    · intro z hz
      -- surjectivity by counting
      have hinj : Set.InjOn (fun x => y * x) Ω := by
        intro x _ x' _ h
        have hy0 : y ≠ 0 := fun e => h0 (e ▸ hy)
        exact mul_left_cancel₀ hy0 h
      have himg : Ω.image (fun x => y * x) = Ω := by
        apply Finset.eq_of_subset_of_card_le
        · intro w hw
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
          exact hmul y hy x hx
        · rw [Finset.card_image_of_injOn hinj]
      rw [← himg] at hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      exact ⟨x, hx, rfl⟩
    · intro x _; rfl
  have : y ^ j * ∑ x ∈ Ω, x ^ j = ∑ x ∈ Ω, x ^ j := by
    rw [Finset.mul_sum, ← hperm]; simp [mul_pow]
  have h' : (y ^ j - 1) * ∑ x ∈ Ω, x ^ j = 0 := by rw [sub_mul, this, one_mul, sub_self]
  rcases mul_eq_zero.1 h' with h | h
  · exact absurd (sub_eq_zero.1 h) hyj
  · exact h

lemma finrank_dualCode {α : Type} [Fintype α] (U : Submodule F (α → F)) :
    Module.finrank F (dualCode U) + Module.finrank F U = Fintype.card α := by
  have hmap : (dualCode U).map (dotProductEquiv F α : (α → F) →ₗ[F] Module.Dual F (α → F)) =
      U.dualAnnihilator := by
    ext φ
    simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator]
    constructor
    · rintro ⟨y, hy, rfl⟩ w hw
      simp only [LinearEquiv.coe_coe, dotProductEquiv_apply_apply]
      rw [dotProduct_comm]; exact hy w hw
    · intro h
      refine ⟨(dotProductEquiv F α).symm φ, ?_, by simp⟩
      intro w hw
      have := h w hw
      rw [dotProduct_comm]
      have key : (dotProductEquiv F α).symm φ ⬝ᵥ w = φ w := by
        conv_rhs => rw [← (dotProductEquiv F α).apply_symm_apply φ]
        rfl
      rw [key]; exact this
  have h1 := LinearEquiv.finrank_map_eq (dotProductEquiv F α) (dualCode U)
  rw [hmap] at h1
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  rw [Module.finrank_fintype_fun_eq_card] at h2
  omega

variable (Ω : Finset F)

lemma evalOn_injOn (d : ℕ) (hd : d ≤ Ω.card) (p : F[X]) (hp : p ∈ degreeLT F d)
    (h0 : evalOn (Ω : Set F) p = 0) : p = 0 := by
  rw [mem_degreeLT] at hp
  by_cases hp0 : p = 0
  · exact hp0
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p Ω
  · intro x hx
    have := congrFun h0 ⟨x, by simpa using hx⟩
    simpa [evalOn] using this
  · have := (natDegree_lt_iff_degree_lt hp0).2 hp
    omega

lemma finrank_rsCode (d : ℕ) (hd : d ≤ Ω.card) :
    Module.finrank F (rsCode (Ω : Set F) d) = d := by
  unfold rsCode
  let f : degreeLT F d →ₗ[F] (↥(Ω : Set F) → F) := (evalOn (Ω : Set F)).comp (degreeLT F d).subtype
  have hrange : (degreeLT F d).map (evalOn (Ω : Set F)) = LinearMap.range f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hrange]
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    exact Subtype.ext (evalOn_injOn Ω d hd p.1 p.2 hp)
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, finrank_bot, add_zero] at this
  rw [this, (degreeLTEquiv F d).finrank_eq, Module.finrank_fin_fun]

/-- the diagonal map as a linear equivalence -/
def monoEquiv {α : Type} (c : α → Fˣ) : (α → F) ≃ₗ[F] (α → F) where
  toFun x ω := (c ω : F) * x ω
  map_add' x y := by funext ω; simp [mul_add]
  map_smul' a x := by funext ω; simp [mul_left_comm]
  invFun x ω := ((c ω)⁻¹ : Fˣ) * x ω
  left_inv x := by funext ω; simp
  right_inv x := by funext ω; simp

lemma monomialImage_eq {α : Type} (c : α → Fˣ) (C : Submodule F (α → F)) :
    monomialImage (Equiv.refl α) c C = C.map (monoEquiv c : (α → F) →ₗ[F] (α → F)) := by
  unfold monomialImage
  congr 1

lemma finrank_monomialImage {α : Type} (c : α → Fˣ) (C : Submodule F (α → F)) :
    Module.finrank F (monomialImage (Equiv.refl α) c C) = Module.finrank F C := by
  rw [monomialImage_eq]; exact LinearEquiv.finrank_map_eq _ _

lemma mem_monomialImage {α : Type} (c : α → Fˣ) (C : Submodule F (α → F)) (x : α → F) :
    x ∈ monomialImage (Equiv.refl α) c C ↔ (fun ω => ((c ω)⁻¹ : Fˣ) * x ω) ∈ C := by
  rw [monomialImage_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : (fun ω => ((c ω)⁻¹ : Fˣ) * ((monoEquiv c : (α → F) →ₗ[F] (α → F)) y) ω) = y := by
      funext ω; simp [monoEquiv]
    rw [this]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    funext ω; simp [monoEquiv]

end PrivPCP.RSD


namespace PrivPCP.RSD

open GoodQLTC Classical PrivPCP.TDual Polynomial

variable {F : Type} [Field F] [Fintype F]

lemma card_sub (Ω : Finset F) : Fintype.card ↥(Ω : Set F) = Ω.card := by simp

lemma sum_sub (Ω : Finset F) (f : F → F) : ∑ x : ↥(Ω : Set F), f x = ∑ x ∈ Ω, f x :=
  Finset.sum_coe_sort Ω f

lemma dual_monomialImage {α : Type} [Fintype α] (c : α → Fˣ) (C : Submodule F (α → F)) :
    dualCode (monomialImage (Equiv.refl α) c C) = monomialImage (Equiv.refl α) c⁻¹ (dualCode C) := by
  ext y
  rw [mem_monomialImage, mem_dualCode, mem_dualCode]
  constructor
  · intro h v hv
    have hw : (fun ω => (c ω : F) * v ω) ∈ monomialImage (Equiv.refl α) c C := by
      rw [mem_monomialImage]; convert hv using 1; funext ω; simp
    have := h _ hw
    rw [← this]
    simp only [dotProduct, Pi.inv_apply, inv_inv]
    refine Finset.sum_congr rfl fun ω _ => by ring
  · intro h w hw
    rw [mem_monomialImage] at hw
    have := h _ hw
    rw [← this]
    simp only [dotProduct, Pi.inv_apply, inv_inv]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [Units.val_inv_eq_inv_val]
    have : (c ω : F) ≠ 0 := (c ω).ne_zero
    field_simp

lemma monomialImage_comp {α : Type} (c c' : α → Fˣ) (C : Submodule F (α → F)) :
    monomialImage (Equiv.refl α) c (monomialImage (Equiv.refl α) c' C) =
      monomialImage (Equiv.refl α) (c * c') C := by
  ext x
  rw [mem_monomialImage, mem_monomialImage, mem_monomialImage]
  have : (fun ω => (((c' ω)⁻¹ : Fˣ) : F) * ((((c ω)⁻¹ : Fˣ) : F) * x ω)) =
      (fun ω => ((((c * c') ω)⁻¹ : Fˣ) : F) * x ω) := by
    funext ω; simp [mul_inv_rev]; ring
  rw [this]

variable (Ω : Finset F) (hmul : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y ∈ Ω) (h0 : (0 : F) ∉ Ω)

/-- the coordinate as a unit -/
noncomputable def ux (h0 : (0 : F) ∉ Ω) : ↥(Ω : Set F) → Fˣ :=
  fun x => Units.mk0 x.1 (fun e => h0 (e ▸ (by simpa using x.2)))

include hmul in
theorem dual_rs (d : ℕ) (hd : d ≤ Ω.card) :
    dualCode (rsCode (Ω : Set F) d) =
      monomialImage (Equiv.refl _) (ux Ω h0) (rsCode (Ω : Set F) (Ω.card - d)) := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro w hw
    rw [mem_monomialImage] at hw
    obtain ⟨g, hg, hge⟩ := hw
    rw [SetLike.mem_coe, mem_degreeLT] at hg
    intro v hv
    obtain ⟨f, hf, rfl⟩ := hv
    rw [SetLike.mem_coe, mem_degreeLT] at hf
    have hw' : ∀ x : ↥(Ω : Set F), w x = x.1 * g.eval x.1 := by
      intro x
      have := congrFun hge x
      simp only [evalOn, LinearMap.coe_mk, AddHom.coe_mk, ux] at this
      rw [this]
      have hx : (x.1 : F) ≠ 0 := fun e => h0 (e ▸ (by simpa using x.2))
      simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    let h : F[X] := f * (X * g)
    have hdot : evalOn (Ω : Set F) f ⬝ᵥ w = ∑ x ∈ Ω, h.eval x := by
      rw [dotProduct]
      rw [← sum_sub Ω (fun x => h.eval x)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hw' x]
      simp [evalOn, h]
    rw [hdot]
    rcases Nat.eq_zero_or_pos Ω.card with hΩ | hΩ
    · rw [Finset.card_eq_zero.1 hΩ, Finset.sum_empty]
    have hdeg : h.natDegree < Ω.card := by
      by_cases hf0 : f = 0
      · simp only [h, hf0, zero_mul, natDegree_zero]; exact hΩ
      by_cases hg0 : g = 0
      · simp only [h, hg0, mul_zero, natDegree_zero]; exact hΩ
      have h1 := (natDegree_lt_iff_degree_lt hf0).2 hf
      have h2 := (natDegree_lt_iff_degree_lt hg0).2 hg
      have h3 : h.natDegree ≤ f.natDegree + (1 + g.natDegree) := by
        refine (natDegree_mul_le).trans (Nat.add_le_add_left ?_ _)
        exact (natDegree_mul_le).trans (Nat.add_le_add_right natDegree_X_le _)
      omega
    simp_rw [eval_eq_sum_range' hdeg]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [← Finset.mul_sum]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp [h, mul_coeff_zero]
    · rw [powsum Ω hmul h0 j hjpos (Finset.mem_range.1 hj), mul_zero]
  · rw [finrank_monomialImage, finrank_rsCode Ω _ (Nat.sub_le _ _)]
    have := finrank_dualCode (rsCode (Ω : Set F) d)
    rw [finrank_rsCode Ω d hd, card_sub] at this
    omega

end PrivPCP.RSD


namespace PrivPCP.RSD

open GoodQLTC Classical PrivPCP.TDual Polynomial

variable {F : Type} [Field F] [Fintype F]
variable (Ω H : Finset F)

noncomputable def Zp : F[X] := ∏ c ∈ H, (X - C c)

lemma Zp_monic : (Zp H).Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C c

lemma Zp_natDegree : (Zp H).natDegree = H.card := by
  rw [Zp, natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]; simp

lemma Zp_eval (x : F) : (Zp H).eval x = ∏ c ∈ H, (x - c) := by simp [Zp, eval_prod]

noncomputable def Zu (hdisj : Disjoint H Ω) : ↥(Ω : Set F) → Fˣ :=
  fun x => Units.mk0 (∏ c ∈ H, (x.1 - c)) (by
    rw [Finset.prod_ne_zero_iff]
    intro c hc e
    rw [sub_eq_zero] at e
    exact Finset.disjoint_left.1 hdisj hc (e ▸ (by simpa using x.2)))

lemma Zp_dvd (p : F[X]) (hv : ∀ c ∈ H, p.eval c = 0) : Zp H ∣ p := by
  by_cases hp : p = 0
  · rw [hp]; exact dvd_zero _
  have : (H.val.map fun a => X - C a).prod ∣ p := by
    rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hp]
    rw [Multiset.le_iff_subset H.nodup]
    intro c hc
    rw [mem_roots hp]
    exact hv c hc
  have e : Zp H = (H.val.map fun a => X - C a).prod := by rw [Zp, Finset.prod_eq_multiset_prod]
  rw [e]; exact this

theorem vanish_eq (a : ℕ) (hHa : H.card ≤ a) (hdisj : Disjoint H Ω) :
    vanishCode Ω H a = monomialImage (Equiv.refl _) (Zu Ω H hdisj)
      (rsCode (Ω : Set F) (a - H.card + 1)) := by
  ext w
  rw [mem_monomialImage]
  constructor
  · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
    rw [SetLike.mem_coe, mem_degreeLT] at hp1
    have hv : ∀ c ∈ H, p.eval c = 0 := by
      simpa only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, leval_apply] using hp2
    obtain ⟨q, rfl⟩ := Zp_dvd H p hv
    refine ⟨q, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_degreeLT]
      by_cases hq : q = 0
      · simp [hq]
      have hZ0 : Zp H ≠ 0 := (Zp_monic H).ne_zero
      have hpq : Zp H * q ≠ 0 := mul_ne_zero hZ0 hq
      have h1 := (natDegree_lt_iff_degree_lt hpq).2 hp1
      rw [natDegree_mul hZ0 hq, Zp_natDegree] at h1
      rw [degree_eq_natDegree hq]
      exact_mod_cast (show q.natDegree < a - H.card + 1 by omega)
    · funext x
      simp only [evalOn, LinearMap.coe_mk, AddHom.coe_mk, eval_mul, Zp_eval, Zu,
        Units.val_inv_eq_inv_val, Units.val_mk0]
      have : ∏ c ∈ H, ((x : F) - c) ≠ 0 := (Zu Ω H hdisj x).ne_zero
      field_simp
  · rintro ⟨q, hq, hqe⟩
    rw [SetLike.mem_coe, mem_degreeLT] at hq
    refine ⟨Zp H * q, ⟨?_, ?_⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_degreeLT]
      by_cases hq0 : q = 0
      · simp [hq0]
      have hZ0 : Zp H ≠ 0 := (Zp_monic H).ne_zero
      rw [degree_eq_natDegree (mul_ne_zero hZ0 hq0), natDegree_mul hZ0 hq0, Zp_natDegree]
      have := (natDegree_lt_iff_degree_lt hq0).2 hq
      exact_mod_cast (show H.card + q.natDegree < a + 1 by omega)
    · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, leval_apply]
      intro c hc
      rw [eval_mul, Zp_eval, Finset.prod_eq_zero hc (sub_self c), zero_mul]
    · funext x
      have := congrFun hqe x
      simp only [evalOn, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
      rw [eval_mul, Zp_eval, this]
      simp only [Zu, Units.val_inv_eq_inv_val, Units.val_mk0]
      have : ∏ c ∈ H, ((x : F) - c) ≠ 0 := (Zu Ω H hdisj x).ne_zero
      field_simp

/-- Reed–Solomon distance -/
theorem rs_weight (c : ↥(Ω : Set F) → Fˣ) (t : ℕ) (w : ↥(Ω : Set F) → F)
    (hw : w ∈ monomialImage (Equiv.refl _) c (rsCode (Ω : Set F) t)) (hw0 : w ≠ 0) :
    Ω.card + 1 ≤ supportCard w + t := by
  rw [mem_monomialImage] at hw
  obtain ⟨p, hp, hpe⟩ := hw
  rw [SetLike.mem_coe, mem_degreeLT] at hp
  have hp0 : p ≠ 0 := by
    intro hp0
    apply hw0; funext x
    have := congrFun hpe x
    have h' : (((c x)⁻¹ : Fˣ) : F) * w x = 0 := by
      rw [← this]; simp [evalOn, hp0]
    exact (mul_eq_zero.1 h').resolve_left (Units.ne_zero _)
  have hzero : ∀ x : ↥(Ω : Set F), w x = 0 ↔ p.eval x.1 = 0 := by
    intro x
    have := congrFun hpe x
    simp only [evalOn, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this]
    simp [(c x)⁻¹.ne_zero]
  have hroots : (Finset.univ.filter fun x : ↥(Ω : Set F) => w x = 0).card ≤ t - 1 := by
    have h1 : (Finset.univ.filter fun x : ↥(Ω : Set F) => w x = 0).card ≤ p.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun x => x.1)
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
        simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp0, IsRoot.def]
        exact (hzero x).1 hx
      · intro x _ y _ h; exact Subtype.ext h
    have h2 := Multiset.toFinset_card_le p.roots
    have h3 := card_roots' p
    have h4 := (natDegree_lt_iff_degree_lt hp0).2 hp
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ↥(Ω : Set F))) (fun x => w x = 0)
  rw [Finset.card_univ, card_sub] at hsplit
  unfold supportCard
  have ht : 1 ≤ t := by
    by_contra h0; push Not at h0
    have : t = 0 := by omega
    subst this
    have := (natDegree_lt_iff_degree_lt hp0).2 hp
    omega
  simp only [ne_eq] at hsplit ⊢
  omega

end PrivPCP.RSD


namespace PrivPCP.R411

open GoodQLTC Classical PrivPCP.TDual PrivPCP.RSD

variable {F : Type} [Field F] [Fintype F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

/-- the diagonal scaling of words -/
def dscale (Λ : ∀ i, S i → Fˣ) (x : (∀ i, S i) → F) : (∀ i, S i) → F :=
  fun ω => (∏ j, (Λ j (ω j) : F)) * x ω

lemma dscale_ne (Λ : ∀ i, S i → Fˣ) (ω : ∀ i, S i) : (∏ j, (Λ j (ω j) : F)) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => (Λ j (ω j)).ne_zero

lemma dscale_inv (Λ : ∀ i, S i → Fˣ) (x : (∀ i, S i) → F) :
    dscale Λ (dscale (fun i s => (Λ i s)⁻¹) x) = x := by
  funext ω; simp only [dscale]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  simp

lemma dscale_add (Λ : ∀ i, S i → Fˣ) (x y : (∀ i, S i) → F) :
    dscale Λ (x + y) = dscale Λ x + dscale Λ y := by funext ω; simp [dscale, mul_add]

lemma dscale_sum (Λ : ∀ i, S i → Fˣ) (y : ι → (∀ i, S i) → F) :
    dscale Λ (∑ i, y i) = ∑ i, dscale Λ (y i) := by
  funext ω; simp [dscale, Finset.mul_sum, Finset.sum_apply]

lemma dscale_ne_zero_iff (Λ : ∀ i, S i → Fˣ) (x : (∀ i, S i) → F) (ω : ∀ i, S i) :
    dscale Λ x ω ≠ 0 ↔ x ω ≠ 0 := by
  simp only [dscale, ne_eq, mul_eq_zero, not_or]
  exact ⟨fun h => h.2, fun h => ⟨dscale_ne Λ ω, h⟩⟩

/-- scaling maps axis codes of `C` to axis codes of the rescaled codes -/
lemma dscale_axis (Λ : ∀ i, S i → Fˣ) (C : ∀ i, Submodule F (S i → F)) (i : ι)
    (x : (∀ i, S i) → F) (hx : x ∈ axisCode C i) :
    dscale Λ x ∈ axisCode (fun j => monomialImage (Equiv.refl _) (Λ j) (C j)) i := by
  rw [mem_axisCode_iff] at hx ⊢
  intro b
  rw [mem_monomialImage]
  have : (fun s => (((Λ i s)⁻¹ : Fˣ) : F) * dscale Λ x (Function.update b i s)) =
      (∏ j ∈ Finset.univ.erase i, (Λ j (b j) : F)) • (fun s => x (Function.update b i s)) := by
    funext s
    simp only [dscale, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    have hprod : ∏ j ∈ Finset.univ.erase i, (Λ j (Function.update b i s j) : F) =
        ∏ j ∈ Finset.univ.erase i, (Λ j (b j) : F) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hprod]
    have := (Λ i s).ne_zero
    field_simp
    simp
  rw [this]
  exact (C i).smul_mem _ (hx b)

lemma dscale_axis_inv (Λ : ∀ i, S i → Fˣ) (C : ∀ i, Submodule F (S i → F)) (i : ι)
    (x : (∀ i, S i) → F) (hx : x ∈ axisCode (fun j => monomialImage (Equiv.refl _) (Λ j) (C j)) i) :
    dscale (fun i s => (Λ i s)⁻¹) x ∈ axisCode C i := by
  rw [mem_axisCode_iff] at hx ⊢
  intro b
  have hb := hx b
  rw [mem_monomialImage] at hb
  have : (fun s => dscale (fun i s => (Λ i s)⁻¹) x (Function.update b i s)) =
      (∏ j ∈ Finset.univ.erase i, (((Λ j (b j))⁻¹ : Fˣ) : F)) •
        (fun s => (((Λ i s)⁻¹ : Fˣ) : F) * x (Function.update b i s)) := by
    funext s
    simp only [dscale, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    have hprod : ∏ j ∈ Finset.univ.erase i, (((Λ j (Function.update b i s j))⁻¹ : Fˣ) : F) =
        ∏ j ∈ Finset.univ.erase i, (((Λ j (b j))⁻¹ : Fˣ) : F) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hprod]; ring
  rw [this]
  exact (C i).smul_mem _ hb

/-- **rescaling preserves product expansion** -/
theorem pe_rescale (Λ : ∀ i, S i → Fˣ) (C : ∀ i, Submodule F (S i → F)) (ρ : ℝ)
    (h : IsProductExpanding ρ C) :
    IsProductExpanding ρ (fun i => monomialImage (Equiv.refl _) (Λ i) (C i)) := by
  refine ⟨h.1, fun x hx => ?_⟩
  set Λ' : ∀ i, S i → Fˣ := fun i s => (Λ i s)⁻¹
  have hx' : dscale Λ' x ∈ ⨆ i, axisCode C i := by
    refine Submodule.iSup_induction _ (motive := fun x => dscale Λ' x ∈ ⨆ i, axisCode C i) hx ?_ ?_ ?_
    · intro i y hy; exact Submodule.mem_iSup_of_mem i (dscale_axis_inv Λ C i y hy)
    · have : dscale Λ' (0 : (∀ i, S i) → F) = 0 := by funext ω; simp [dscale]
      rw [this]; exact Submodule.zero_mem _
    · intro a b ha hb; rw [dscale_add]; exact Submodule.add_mem _ ha hb
  obtain ⟨y, hy, hsum, hbd⟩ := h.2 _ hx'
  refine ⟨fun i => dscale Λ (y i), fun i => dscale_axis Λ C i (y i) (hy i), ?_, ?_⟩
  · rw [← dscale_sum, ← hsum, dscale_inv]
  · have hl : ∀ i, lineCount i (dscale Λ (y i)) = lineCount i (y i) := by
      intro i; unfold lineCount; congr 2; ext ω; simp only [Finset.mem_filter, Finset.mem_univ,
        true_and]; exact dscale_ne_zero_iff Λ (y i) ω
    have hs : supportCard (dscale Λ' x) = supportCard x := by
      unfold supportCard; congr 1; ext ω; simp only [Finset.mem_filter, Finset.mem_univ,
        true_and]; exact dscale_ne_zero_iff Λ' x ω
    simp_rw [hl]
    rw [← hs]; exact hbd

end PrivPCP.R411


namespace PrivPCP.Fact33Aux

open MvPolynomial

variable {F : Type} [Field F] {k : ℕ}

lemma degreeOf_monomial_le' (s : Fin k →₀ ℕ) (c : F) (j : Fin k) :
    (monomial s c : MvPolynomial (Fin k) F).degreeOf j ≤ s j := by
  rw [degreeOf_le_iff]
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

lemma degreeOf_aeval_X_le (i j : Fin k) (p : Polynomial F) :
    (Polynomial.aeval (X i : MvPolynomial (Fin k) F) p).degreeOf j ≤
      if j = i then p.natDegree else 0 := by
  rw [Polynomial.aeval_eq_sum_range]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun n hn => ?_)
  rw [MvPolynomial.smul_eq_C_mul]
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  split_ifs with h
  · subst h
    rw [degreeOf_X_self_pow]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  · rw [degreeOf_X_pow_of_ne _ h]

lemma le_degreeOf_of_mem {R : MvPolynomial (Fin k) F} {e : Fin k →₀ ℕ} (he : e ∈ R.support)
    (j : Fin k) : e j ≤ R.degreeOf j :=
  (degreeOf_le_iff.mp le_rfl) e he

/-- quotient of division by `Z(X_i)` -/
noncomputable def divQ (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    MvPolynomial (Fin k) F :=
  ∑ e ∈ R.support, monomial (Finsupp.update e i 0) (R.coeff e) *
    Polynomial.aeval (X i) (Polynomial.X ^ (e i) /ₘ Z)

/-- remainder of division by `Z(X_i)` -/
noncomputable def divR (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    MvPolynomial (Fin k) F :=
  ∑ e ∈ R.support, monomial (Finsupp.update e i 0) (R.coeff e) *
    Polynomial.aeval (X i) (Polynomial.X ^ (e i) %ₘ Z)

lemma div_eq (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    R = Polynomial.aeval (X i) Z * divQ i Z R + divR i Z R := by
  conv_lhs => rw [as_sum R]
  unfold divQ divR
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : (monomial e (R.coeff e) : MvPolynomial (Fin k) F) =
      monomial (Finsupp.update e i 0) (R.coeff e) * X i ^ (e i) := by
    have hs : Finsupp.update e i 0 + Finsupp.single i (e i) = e := by
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Finsupp.update_apply, hj, Finsupp.single_apply, Ne.symm hj]
    rw [X_pow_eq_monomial, monomial_mul, mul_one, hs]
  have h2 : (X i : MvPolynomial (Fin k) F) ^ (e i) =
      Polynomial.aeval (X i) (Polynomial.X ^ (e i) %ₘ Z + Z * (Polynomial.X ^ (e i) /ₘ Z)) := by
    rw [Polynomial.modByMonic_add_div]; simp
  rw [h1, h2, map_add, map_mul]
  ring

lemma divQ_degreeOf (i : Fin k) (Z : Polynomial F) (hZ : Z.Monic) (R : MvPolynomial (Fin k) F)
    (j : Fin k) :
    (divQ i Z R).degreeOf j ≤ if j = i then R.degreeOf i - Z.natDegree else R.degreeOf j := by
  unfold divQ
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
  split_ifs with h
  · subst h
    have h0 : (Finsupp.update e j 0) j = 0 := by simp
    rw [h0, zero_add]
    rw [Polynomial.natDegree_divByMonic _ hZ, Polynomial.natDegree_X_pow]
    exact Nat.sub_le_sub_right (le_degreeOf_of_mem he j) _
  · simp only [Finsupp.update_apply, h, if_false, add_zero]
    exact le_degreeOf_of_mem he j

lemma divR_degreeOf_ne (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F)
    (j : Fin k) (hj : j ≠ i) : (divR i Z R).degreeOf j ≤ R.degreeOf j := by
  unfold divR
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
  simp only [Finsupp.update_apply, hj, if_false, add_zero]
  exact le_degreeOf_of_mem he j

lemma divR_degreeOf_self (i : Fin k) (Z : Polynomial F) (hZ : Z.Monic) (hZ1 : Z ≠ 1)
    (R : MvPolynomial (Fin k) F) : (divR i Z R).degreeOf i < Z.natDegree := by
  have hpos : 0 < Z.natDegree := by
    rcases Nat.eq_zero_or_pos Z.natDegree with h | h
    · exact absurd (Polynomial.eq_one_of_monic_natDegree_zero hZ h) hZ1
    · exact h
  have : (divR i Z R).degreeOf i ≤ Z.natDegree - 1 := by
    unfold divR
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
    refine (degreeOf_mul_le _ _ _).trans ?_
    refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
    have h0 : (Finsupp.update e i 0) i = 0 := by simp
    simp only [h0, if_true, zero_add]
    have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ (e i)) hZ hZ1
    omega
  omega

end PrivPCP.Fact33Aux


namespace PrivPCP.L62Aux

open MvPolynomial PrivPCP.Fact33Aux Classical

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

/-- univariate restriction of `R` to the `j`-line through `x` -/
noncomputable def lineRestr (R : MvPolynomial (Fin k) F) (j : Fin k) (x : Fin k → F) :
    Polynomial F :=
  aeval (fun l => if l = j then Polynomial.X else Polynomial.C (x l)) R

lemma eval_lineRestr (R : MvPolynomial (Fin k) F) (j : Fin k) (x : Fin k → F) (t : F) :
    (lineRestr R j x).eval t = eval (Function.update x j t) R := by
  unfold lineRestr
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul, aeval_X, eval_X]
    congr 1
    by_cases h : i = j
    · subst h; simp
    · simp [h, Function.update_of_ne h]

lemma natDegree_lineRestr (R : MvPolynomial (Fin k) F) (j : Fin k) (x : Fin k → F) :
    (lineRestr R j x).natDegree ≤ R.degreeOf j := by
  unfold lineRestr
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ l, ((if l = j then Polynomial.X else Polynomial.C (x l)) ^ m l : Polynomial F).natDegree
      ≤ ∑ l, if l = j then m l else 0 := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine (Polynomial.natDegree_pow_le).trans ?_
        split_ifs with h
        · have := Polynomial.natDegree_X_le (R := F); nlinarith
        · simp
    _ = m j := by simp
    _ ≤ R.degreeOf j := le_degreeOf_of_mem hm j

lemma lineRestr_mul (R R' : MvPolynomial (Fin k) F) (j : Fin k) (x : Fin k → F) :
    lineRestr (R * R') j x = lineRestr R j x * lineRestr R' j x := by
  unfold lineRestr; rw [map_mul]

lemma cardS (S : Fin k → Finset F) (j : Fin k) :
    Fintype.card ↥((S j : Finset F) : Set F) = (S j).card := by simp

/-- the grid point as a point of `F^k` -/
def gpt (S : Fin k → Finset F) (x : Grid S) : Fin k → F := fun l => (x l : F)

lemma evGrid_eq (S : Fin k → Finset F) (P : MvPolynomial (Fin k) F) (x : Grid S) :
    evGrid S P x = eval (gpt S x) P := rfl

/-- Lagrange basis polynomial on the side `S j` -/
noncomputable def lb (S : Fin k → Finset F) (j : Fin k) (t : ↥((S j : Finset F) : Set F)) :
    Polynomial F :=
  Lagrange.basis (Finset.univ : Finset ↥((S j : Finset F) : Set F)) Subtype.val t

lemma injOn_val (S : Fin k → Finset F) (j : Fin k) :
    Set.InjOn (Subtype.val : ↥((S j : Finset F) : Set F) → F)
      ((Finset.univ : Finset ↥((S j : Finset F) : Set F)) : Set _) :=
  Subtype.val_injective.injOn

lemma eval_lb (S : Fin k → Finset F) (j : Fin k) (t t' : ↥((S j : Finset F) : Set F)) :
    (lb S j t).eval (t' : F) = if t = t' then 1 else 0 := by
  unfold lb
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self (injOn_val S j) (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ _)

lemma natDegree_lb (S : Fin k → Finset F) (j : Fin k) (t : ↥((S j : Finset F) : Set F)) :
    (lb S j t).natDegree < (S j).card := by
  unfold lb
  rw [Lagrange.natDegree_basis (injOn_val S j) (Finset.mem_univ _)]
  have : 0 < (Finset.univ : Finset ↥((S j : Finset F) : Set F)).card :=
    Finset.card_pos.mpr ⟨t, Finset.mem_univ _⟩
  rw [Finset.card_univ, cardS] at this ⊢
  omega

/-- interpolant of the `j`-line of `w` through `y` -/
noncomputable def lineInterp (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k) (y : Grid S) :
    Polynomial F :=
  Lagrange.interpolate (Finset.univ : Finset ↥((S j : Finset F) : Set F)) Subtype.val
    (fun t => w (Function.update y j t))

lemma eval_lineInterp (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k) (y : Grid S)
    (t : ↥((S j : Finset F) : Set F)) :
    (lineInterp S w j y).eval (t : F) = w (Function.update y j t) :=
  Lagrange.eval_interpolate_at_node _ (injOn_val S j) (Finset.mem_univ _)

/-- if the line is a polynomial of small degree, the interpolant equals it -/
lemma lineInterp_eq (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k) (y : Grid S)
    (p : Polynomial F) (hp : p.degree < (S j).card)
    (hev : ∀ t : ↥((S j : Finset F) : Set F), p.eval (t : F) = w (Function.update y j t)) :
    lineInterp S w j y = p := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _ (injOn_val S j)
  · rw [Finset.card_univ, cardS]; exact hp
  · intro t _; exact hev t

/-- the regrouped Lagrange interpolant along direction `j` -/
noncomputable def Pj (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) : MvPolynomial (Fin k) F :=
  ∑ y ∈ Finset.univ.filter (fun y : Grid S => y j = t0),
    (∏ l ∈ Finset.univ.erase j, Polynomial.aeval (X l) (lb S l (y l))) *
      Polynomial.aeval (X j) (lineInterp S w j y)

lemma eval_aeval_X (p : Polynomial F) (l : Fin k) (z : Fin k → F) :
    eval z (Polynomial.aeval (X l : MvPolynomial (Fin k) F) p) = p.eval (z l) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

lemma eval_Pj (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) (x : Grid S) (c : F) :
    eval (Function.update (gpt S x) j c) (Pj S w j t0) =
      (lineInterp S w j (Function.update x j t0)).eval c := by
  unfold Pj
  rw [map_sum]
  rw [Finset.sum_eq_single (Function.update x j t0)]
  · rw [map_mul, eval_aeval_X, map_prod, Function.update_self]
    rw [Finset.prod_eq_one, one_mul]
    intro l hl
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    rw [eval_aeval_X, Function.update_of_ne hlj, Function.update_of_ne hlj]
    unfold gpt
    rw [eval_lb, if_pos rfl]
  · intro y hy hne
    rw [Finset.mem_filter] at hy
    have : ∃ l, l ≠ j ∧ y l ≠ x l := by
      by_contra hcon
      push Not at hcon
      apply hne
      funext l
      by_cases hl : l = j
      · subst hl; rw [Function.update_self, hy.2]
      · rw [Function.update_of_ne hl]; exact hcon l hl
    obtain ⟨l, hlj, hl⟩ := this
    rw [map_mul, map_prod]
    rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨hlj, Finset.mem_univ _⟩), zero_mul]
    rw [eval_aeval_X, Function.update_of_ne hlj]
    unfold gpt
    rw [eval_lb, if_neg hl]
  · intro h
    exfalso; apply h
    simp

lemma evGrid_Pj (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) : evGrid S (Pj S w j t0) = w := by
  funext x
  rw [evGrid_eq]
  have : gpt S x = Function.update (gpt S x) j (x j : F) := by simp [gpt]
  rw [this, eval_Pj, eval_lineInterp]
  congr 1
  funext l
  by_cases hl : l = j
  · subst hl; simp [gpt]
  · simp [Function.update_of_ne hl]

end PrivPCP.L62Aux


namespace PrivPCP.L62Aux

open MvPolynomial PrivPCP.Fact33Aux Classical

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

lemma degreeOf_prod_aeval_le (S : Fin k → Finset F) (j l : Fin k) (y : Grid S) :
    (∏ m ∈ Finset.univ.erase j, Polynomial.aeval (X m : MvPolynomial (Fin k) F) (lb S m (y m))).degreeOf l
      ≤ if l = j then 0 else (S l).card - 1 := by
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ m ∈ Finset.univ.erase j,
        (Polynomial.aeval (X m : MvPolynomial (Fin k) F) (lb S m (y m))).degreeOf l
      ≤ ∑ m ∈ Finset.univ.erase j, if l = m then (S l).card - 1 else 0 := by
        refine Finset.sum_le_sum fun m _ => (degreeOf_aeval_X_le m l _).trans ?_
        split_ifs with h
        · subst h; have := natDegree_lb S l (y l); omega
        · exact le_rfl
    _ = if l = j then 0 else (S l).card - 1 := by
        rw [Finset.sum_ite_eq]
        by_cases h : l = j
        · subst h; simp
        · simp [h]

lemma degreeOf_Pj_ne (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) (l : Fin k) (hl : l ≠ j) :
    (Pj S w j t0).degreeOf l ≤ (S l).card - 1 := by
  unfold Pj
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun y _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_prod_aeval_le S j l y
  rw [if_neg hl] at h1
  have h2 := degreeOf_aeval_X_le j l (lineInterp S w j y)
  rw [if_neg hl] at h2
  omega

lemma degreeOf_Pj_self (S : Fin k → Finset F) (w : Grid S → F) (j : Fin k)
    (t0 : ↥((S j : Finset F) : Set F)) (d : ℕ) (hd : ∀ y, (lineInterp S w j y).natDegree ≤ d) :
    (Pj S w j t0).degreeOf j ≤ d := by
  unfold Pj
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun y _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_prod_aeval_le S j j y
  rw [if_pos rfl] at h1
  have h2 := degreeOf_aeval_X_le j j (lineInterp S w j y)
  rw [if_pos rfl] at h2
  have := hd y
  omega

lemma gpt_mk (S : Fin k → Finset F) (x : Fin k → F) (hx : ∀ l, x l ∈ S l) :
    gpt S (fun l => ⟨x l, hx l⟩ : Grid S) = x := rfl

lemma eq_of_evGrid_eq (S : Fin k → Finset F) (P1 P2 : MvPolynomial (Fin k) F)
    (h1 : ∀ l, P1.degreeOf l < (S l).card) (h2 : ∀ l, P2.degreeOf l < (S l).card)
    (he : evGrid S P1 = evGrid S P2) : P1 = P2 := by
  rw [← sub_eq_zero]
  apply eq_zero_of_eval_zero_at_prod_finset _ S
  · intro l
    exact lt_of_le_of_lt (degreeOf_sub_le _ _ _) (max_lt (h1 l) (h2 l))
  · intro x hx
    have := congrFun he (fun l => ⟨x l, hx l⟩)
    rw [evGrid_eq, evGrid_eq, gpt_mk] at this
    rw [map_sub, this, sub_self]

/-- a line of a tensor-RS word -/
lemma line_mem_rs (S : Fin k → Finset F) (a : Fin k → ℕ) (w : Grid S → F)
    (hw : w ∈ tensorCode (fun l => GoodQLTC.rsCode ((S l : Finset F) : Set F) (a l + 1)))
    (j : Fin k) (y : Grid S) :
    ∃ p : Polynomial F, p.degree < a j + 1 ∧
      ∀ t : ↥((S j : Finset F) : Set F), p.eval (t : F) = w (Function.update y j t) := by
  have hw' := (Submodule.mem_iInf _).1 hw j
  simp only [GoodQLTC.axisCode, Submodule.mem_iInf, Submodule.mem_comap] at hw'
  obtain ⟨p, hp, hpe⟩ := hw' y
  refine ⟨p, Polynomial.mem_degreeLT.1 hp, fun t => ?_⟩
  have := congrFun hpe t
  simpa [GoodQLTC.evalOn] using this

/-- full Lagrange interpolant -/
noncomputable def P0 (S : Fin k → Finset F) (w : Grid S → F) : MvPolynomial (Fin k) F :=
  ∑ x : Grid S, C (w x) * ∏ l, Polynomial.aeval (X l) (lb S l (x l))

lemma evGrid_P0 (S : Fin k → Finset F) (w : Grid S → F) : evGrid S (P0 S w) = w := by
  funext x
  rw [evGrid_eq]
  unfold P0
  rw [map_sum, Finset.sum_eq_single x]
  · rw [map_mul, eval_C, map_prod]
    rw [Finset.prod_eq_one, mul_one]
    intro l _
    rw [eval_aeval_X]; unfold gpt; rw [eval_lb, if_pos rfl]
  · intro y _ hne
    obtain ⟨l, hl⟩ : ∃ l, y l ≠ x l := by
      by_contra h; push Not at h; exact hne (funext h)
    rw [map_mul, map_prod, Finset.prod_eq_zero (i := l) (Finset.mem_univ _), mul_zero]
    rw [eval_aeval_X]; unfold gpt; rw [eval_lb, if_neg hl]
  · simp

lemma degreeOf_P0 (S : Fin k → Finset F) (w : Grid S → F) (hS : ∀ l, 0 < (S l).card) (l : Fin k) :
    (P0 S w).degreeOf l < (S l).card := by
  have : (P0 S w).degreeOf l ≤ (S l).card - 1 := by
    unfold P0
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun y _ => ?_)
    refine (degreeOf_C_mul_le _ _ _).trans ?_
    refine (degreeOf_prod_le _ _ _).trans ?_
    calc ∑ m, (Polynomial.aeval (X m : MvPolynomial (Fin k) F) (lb S m (y m))).degreeOf l
        ≤ ∑ m, if l = m then (S l).card - 1 else 0 := by
          refine Finset.sum_le_sum fun m _ => (degreeOf_aeval_X_le m l _).trans ?_
          split_ifs with h
          · subst h; have := natDegree_lb S l (y l); omega
          · exact le_rfl
      _ = (S l).card - 1 := by simp
  have := hS l
  omega

/-- **Interpolation of tensor Reed–Solomon words** -/
theorem interp (S : Fin k → Finset F) (a : Fin k → ℕ) (ha : ∀ l, a l < (S l).card)
    (w : Grid S → F)
    (hw : w ∈ tensorCode (fun l => GoodQLTC.rsCode ((S l : Finset F) : Set F) (a l + 1))) :
    (∀ l, (P0 S w).degreeOf l ≤ a l) ∧ evGrid S (P0 S w) = w ∧
      ∀ j (t0 : ↥((S j : Finset F) : Set F)), P0 S w = Pj S w j t0 := by
  have hS : ∀ l, 0 < (S l).card := fun l => by have := ha l; omega
  have heq : ∀ j (t0 : ↥((S j : Finset F) : Set F)), P0 S w = Pj S w j t0 := by
    intro j t0
    apply eq_of_evGrid_eq S
    · exact degreeOf_P0 S w hS
    · intro l
      by_cases hl : l = j
      · subst hl
        refine lt_of_le_of_lt (degreeOf_Pj_self S w l t0 (a l) fun y => ?_) (ha l)
        obtain ⟨p, hp, hpe⟩ := line_mem_rs S a w hw l y
        rw [lineInterp_eq S w l y p (lt_of_lt_of_le hp (by exact_mod_cast ha l)) hpe]
        by_cases hp0 : p = 0
        · simp [hp0]
        · have h' := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 (by exact_mod_cast hp)
          omega
      · have := degreeOf_Pj_ne S w j t0 l hl
        have := hS l
        omega
    · rw [evGrid_P0, evGrid_Pj]
  refine ⟨fun l => ?_, evGrid_P0 S w, heq⟩
  obtain ⟨t0, ht0'⟩ := Finset.card_pos.mp (hS l)
  have ht0 : t0 ∈ ((S l : Finset F) : Set F) := by simpa using ht0'
  rw [heq l ⟨t0, ht0⟩]
  refine degreeOf_Pj_self S w l _ (a l) fun y => ?_
  obtain ⟨p, hp, hpe⟩ := line_mem_rs S a w hw l y
  rw [lineInterp_eq S w l y p (lt_of_lt_of_le hp (by exact_mod_cast ha l)) hpe]
  by_cases hp0 : p = 0
  · simp [hp0]
  · have h' := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 (by exact_mod_cast hp)
    omega

end PrivPCP.L62Aux


namespace PrivPCP.R411

open GoodQLTC Classical PrivPCP.RSD MvPolynomial PrivPCP.L62Aux

variable {F : Type} [Field F] [Fintype F]

lemma rs_full (Ω : Finset F) (f : ↥(Ω : Set F) → F) : f ∈ rsCode (Ω : Set F) Ω.card := by
  refine ⟨Lagrange.interpolate (Finset.univ : Finset ↥(Ω : Set F)) Subtype.val f, ?_, ?_⟩
  · rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
    have := Lagrange.degree_interpolate_lt f (s := (Finset.univ : Finset ↥(Ω : Set F)))
      (v := Subtype.val) Subtype.val_injective.injOn
    simpa using this
  · funext t
    simp only [evalOn, LinearMap.coe_mk, AddHom.coe_mk]
    exact Lagrange.eval_interpolate_at_node f Subtype.val_injective.injOn (Finset.mem_univ t)

/-- the row polynomial `Y ↦ P(α, Y)` -/
noncomputable def rowP (α : F) (P : MvPolynomial (Fin 2) F) : Polynomial F :=
  aeval (![Polynomial.C α, Polynomial.X] : Fin 2 → Polynomial F) P

/-- the column polynomial `X ↦ P(X, β)` -/
noncomputable def colP (β : F) (P : MvPolynomial (Fin 2) F) : Polynomial F :=
  aeval (![Polynomial.X, Polynomial.C β] : Fin 2 → Polynomial F) P

lemma rowP_eq (α : F) (P : MvPolynomial (Fin 2) F) : rowP α P = lineRestr P 1 ![α, 0] := by
  unfold rowP lineRestr; congr 2; funext l; fin_cases l <;> simp

lemma colP_eq (β : F) (P : MvPolynomial (Fin 2) F) : colP β P = lineRestr P 0 ![0, β] := by
  unfold colP lineRestr; congr 2; funext l; fin_cases l <;> simp

lemma eval_rowP (α y : F) (P : MvPolynomial (Fin 2) F) : (rowP α P).eval y = eval ![α, y] P := by
  rw [rowP_eq, eval_lineRestr]; congr 2; funext l; fin_cases l <;> simp

lemma eval_colP (β x : F) (P : MvPolynomial (Fin 2) F) : (colP β P).eval x = eval ![x, β] P := by
  rw [colP_eq, eval_lineRestr]; congr 2; funext l; fin_cases l <;> simp

lemma natDegree_rowP (α : F) (P : MvPolynomial (Fin 2) F) : (rowP α P).natDegree ≤ P.degreeOf 1 := by
  rw [rowP_eq]; exact natDegree_lineRestr _ _ _

lemma natDegree_colP (β : F) (P : MvPolynomial (Fin 2) F) : (colP β P).natDegree ≤ P.degreeOf 0 := by
  rw [colP_eq]; exact natDegree_lineRestr _ _ _

lemma rowP_mul (α : F) (P Q : MvPolynomial (Fin 2) F) : rowP α (P * Q) = rowP α P * rowP α Q := by
  unfold rowP; rw [map_mul]

lemma colP_mul (β : F) (P Q : MvPolynomial (Fin 2) F) : colP β (P * Q) = colP β P * colP β Q := by
  unfold colP; rw [map_mul]

lemma rowP_sub (α : F) (P Q : MvPolynomial (Fin 2) F) : rowP α (P - Q) = rowP α P - rowP α Q := by
  unfold rowP; rw [map_sub]

lemma colP_sub (β : F) (P Q : MvPolynomial (Fin 2) F) : colP β (P - Q) = colP β P - colP β Q := by
  unfold colP; rw [map_sub]

lemma rowP_neg (α : F) (P : MvPolynomial (Fin 2) F) : rowP α (-P) = -rowP α P := by
  unfold rowP; rw [map_neg]

lemma gpt2 (Ω : Fin 2 → Finset F) (p : Grid Ω) : gpt Ω p = ![(p 0 : F), (p 1 : F)] := by
  funext l; fin_cases l <;> rfl

/-- univariate uniqueness on a finite set -/
lemma poly_eq_on (s : Finset F) (f g : Polynomial F) (hf : f.natDegree < s.card)
    (hg : g.natDegree < s.card) (h : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq s
  · calc (f - g).degree ≤ max f.degree g.degree := Polynomial.degree_sub_le f g
      _ < s.card := by
        rw [max_lt_iff]
        exact ⟨lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hf),
          lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hg)⟩
  · exact h

/-- a nonzero bivariate polynomial of bidegree `≤ (T,T)` vanishing on a small set -/
lemma exists_vanishing (Sup : Finset (F × F)) (T : ℕ) (hT : Sup.card < (T + 1) * (T + 1)) :
    ∃ E : MvPolynomial (Fin 2) F, E ≠ 0 ∧ E.degreeOf 0 ≤ T ∧ E.degreeOf 1 ≤ T ∧
      ∀ p ∈ Sup, eval ![p.1, p.2] E = 0 := by
  let v : Fin (T + 1) × Fin (T + 1) → (↥Sup → F) := fun ab p => p.1.1 ^ ab.1.val * p.1.2 ^ ab.2.val
  have hnli : ¬ LinearIndependent F v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe] at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hnli
  obtain ⟨c, hc, ⟨ab0, hab0⟩⟩ := hnli
  let E : MvPolynomial (Fin 2) F :=
    ∑ ab : Fin (T + 1) × Fin (T + 1), MvPolynomial.monomial (Finsupp.single 0 ab.1.val + Finsupp.single 1 ab.2.val) (c ab)
  have hcoeff : ∀ ab : Fin (T + 1) × Fin (T + 1),
      E.coeff (Finsupp.single 0 ab.1.val + Finsupp.single 1 ab.2.val) = c ab := by
    intro ab
    simp only [E, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single ab]
    · simp
    · intro ab' _ hne
      rw [if_neg]
      intro h
      apply hne
      have h0 := congrArg (fun f => f 0) h
      have h1 := congrArg (fun f => f 1) h
      simp at h0 h1
      exact Prod.ext (Fin.ext h0) (Fin.ext h1)
    · simp
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro hE
    apply hab0
    rw [← hcoeff ab0, hE, coeff_zero]
  · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun ab _ => ?_)
    rw [degreeOf_le_iff]
    intro m hm
    have := support_monomial_subset hm
    rw [Finset.mem_singleton] at this
    subst this
    simp; omega
  · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun ab _ => ?_)
    rw [degreeOf_le_iff]
    intro m hm
    have := support_monomial_subset hm
    rw [Finset.mem_singleton] at this
    subst this
    simp; omega
  · intro p hp
    have := congrFun hc ⟨p, hp⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at this
    simp only [E, map_sum, eval_monomial]
    rw [← this]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [Finsupp.prod_add_index' (by simp) (by intros; simp [pow_add])]
    simp [Finsupp.prod_single_index]

end PrivPCP.R411


namespace PrivPCP.L62Aux

open MvPolynomial PrivPCP.Fact33Aux Classical

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

/-- the certificate space as a submodule of polynomials -/
def gridQsub (H : Fin k → Finset F) (a : Fin k → ℕ) (i : Fin k) :
    Submodule F (MvPolynomial (Fin k) F) where
  carrier := gridQ H a i
  add_mem' := by
    intro p q hp hq
    refine ⟨(degreeOf_add_le _ _ _).trans (max_le hp.1 hq.1), fun j hj =>
      (degreeOf_add_le _ _ _).trans (max_le (hp.2 j hj) (hq.2 j hj))⟩
  zero_mem' := ⟨by simp, fun j _ => by simp⟩
  smul_mem' := by
    intro c p hp
    rw [smul_eq_C_mul]
    exact ⟨(degreeOf_C_mul_le _ _ _).trans hp.1, fun j hj => (degreeOf_C_mul_le _ _ _).trans (hp.2 j hj)⟩

/-- evaluation on the grid as a linear map -/
noncomputable def evLin (S : Fin k → Finset F) : MvPolynomial (Fin k) F →ₗ[F] (Grid S → F) where
  toFun := evGrid S
  map_add' p q := by funext x; simp [evGrid]
  map_smul' c p := by funext x; simp [evGrid]

/-- `E_i` in certificate form: `{ev(Z_i Q) : Q ∈ Q_i(a)}` -/
noncomputable def Ecert (S H : Fin k → Finset F) (a : Fin k → ℕ) (i : Fin k) :
    Submodule F (Grid S → F) :=
  (gridQsub H a i).map ((evLin S).comp (LinearMap.mulLeft F (gridZ H i)))

lemma mem_Ecert (S H : Fin k → Finset F) (a : Fin k → ℕ) (i : Fin k) (w : Grid S → F) :
    w ∈ Ecert S H a i ↔ ∃ Q ∈ gridQ H a i, evGrid S (gridZ H i * Q) = w := by
  simp [Ecert, evLin, gridQsub]
  rfl

lemma degreeOf_gridZ_ne (H : Fin k → Finset F) (i l : Fin k) (hl : l ≠ i) :
    (gridZ H i).degreeOf l = 0 := by
  unfold gridZ
  apply Nat.eq_zero_of_le_zero
  refine (degreeOf_prod_le _ _ _).trans ?_
  refine (Finset.sum_le_sum fun c _ => (degreeOf_sub_le _ _ _).trans
    (max_le (by rw [degreeOf_X_of_ne hl]) (by rw [degreeOf_C]))).trans ?_
  simp

lemma degreeOf_gridZ_self (H : Fin k → Finset F) (i : Fin k) :
    (gridZ H i).degreeOf i ≤ (H i).card := by
  unfold gridZ
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ c ∈ H i, (X i - C c : MvPolynomial (Fin k) F).degreeOf i ≤ ∑ _c ∈ H i, 1 := by
        refine Finset.sum_le_sum fun c _ => (degreeOf_sub_le _ _ _).trans (max_le ?_ (by simp))
        rw [degreeOf_X_self]
    _ = (H i).card := by simp

lemma mem_rsCode_of (Sl : Finset F) (d : ℕ) (line : ↥((Sl : Finset F) : Set F) → F)
    (p : Polynomial F) (hp : p.natDegree ≤ d)
    (hev : ∀ t : ↥((Sl : Finset F) : Set F), p.eval (t : F) = line t) :
    line ∈ GoodQLTC.rsCode ((Sl : Finset F) : Set F) (d + 1) := by
  refine ⟨p, ?_, ?_⟩
  · rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
  · funext t; simp [GoodQLTC.evalOn, hev]

lemma mem_vanishCode_of (Sl Hl : Finset F) (d : ℕ) (line : ↥((Sl : Finset F) : Set F) → F)
    (p : Polynomial F) (hp : p.natDegree ≤ d) (hv : ∀ c ∈ Hl, p.eval c = 0)
    (hev : ∀ t : ↥((Sl : Finset F) : Set F), p.eval (t : F) = line t) :
    line ∈ vanishCode Sl Hl d := by
  refine ⟨p, ⟨?_, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, Polynomial.leval_apply]
    exact hv
  · funext t; simp [GoodQLTC.evalOn, hev]

lemma of_mem_vanishCode (Sl Hl : Finset F) (d : ℕ) (line : ↥((Sl : Finset F) : Set F) → F)
    (h : line ∈ vanishCode Sl Hl d) :
    ∃ p : Polynomial F, p.degree < d + 1 ∧ (∀ c ∈ Hl, p.eval c = 0) ∧
      ∀ t : ↥((Sl : Finset F) : Set F), p.eval (t : F) = line t := by
  obtain ⟨p, ⟨hp1, hp2⟩, hpe⟩ := h
  refine ⟨p, Polynomial.mem_degreeLT.1 hp1, ?_, fun t => ?_⟩
  · simpa only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, Polynomial.leval_apply]
      using hp2
  · have := congrFun hpe t; simpa [GoodQLTC.evalOn] using this

lemma vanishCode_le (Sl Hl : Finset F) (d : ℕ) :
    vanishCode Sl Hl d ≤ GoodQLTC.rsCode ((Sl : Finset F) : Set F) (d + 1) :=
  Submodule.map_mono inf_le_left

lemma line_eval (S : Fin k → Finset F) (R : MvPolynomial (Fin k) F) (l : Fin k) (y : Grid S)
    (t : ↥((S l : Finset F) : Set F)) :
    evGrid S R (Function.update y l t) = (lineRestr R l (gpt S y)).eval (t : F) := by
  rw [eval_lineRestr, evGrid_eq]
  congr 2
  funext m
  by_cases h : m = l
  · subst h; simp [gpt]
  · simp [gpt, Function.update_of_ne h]

lemma mem_axisCode_iff' {ι : Type} [DecidableEq ι] {Ω : ι → Type}
    (C : ∀ i, Submodule F (Ω i → F)) (i : ι) (x : (∀ i, Ω i) → F) :
    x ∈ GoodQLTC.axisCode C i ↔ ∀ b : (∀ i, Ω i), (fun t => x (Function.update b i t)) ∈ C i := by
  simp only [GoodQLTC.axisCode, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.funLeft_apply]
  exact Iff.rfl

theorem Ecert_le (S H : Fin k → Finset F) (a : Fin k → ℕ) (ha : ∀ i, (H i).card ≤ a i)
    (i : Fin k) :
    Ecert S H a i ≤ (rsNested S H a).E i := by
  intro w hw
  rw [mem_Ecert] at hw
  obtain ⟨Q, hQ, rfl⟩ := hw
  unfold NestedCodes.E tensorCode
  rw [Submodule.mem_iInf]
  intro l
  rw [mem_axisCode_iff']
  intro y
  by_cases hl : l = i
  · subst hl
    rw [Function.update_self]
    refine mem_vanishCode_of _ _ _ _ (lineRestr (gridZ H l * Q) l (gpt S y)) ?_ ?_
      (fun t => (line_eval S _ l y t).symm)
    · refine (natDegree_lineRestr _ _ _).trans ((degreeOf_mul_le _ _ _).trans ?_)
      have := degreeOf_gridZ_self H l
      have := hQ.1
      have := ha l
      omega
    · intro c hc
      rw [eval_lineRestr, map_mul, gridZ, map_prod, Finset.prod_eq_zero hc (by simp), zero_mul]
  · rw [Function.update_of_ne hl]
    refine mem_rsCode_of _ _ _ (lineRestr (gridZ H i * Q) l (gpt S y)) ?_
      (fun t => (line_eval S _ l y t).symm)
    refine (natDegree_lineRestr _ _ _).trans ((degreeOf_mul_le _ _ _).trans ?_)
    rw [degreeOf_gridZ_ne H i l hl, zero_add]
    exact hQ.2 l hl

theorem le_Ecert (S H : Fin k → Finset F) (a : Fin k → ℕ)
    (hSH : ∀ i, 1 ≤ (H i).card ∧ Disjoint (H i) (S i) ∧ (H i).card ≤ a i ∧ a i < (S i).card)
    (i : Fin k) : (rsNested S H a).E i ≤ Ecert S H a i := by
  intro w hw
  have hlines : ∀ l (y : Grid S), (fun t => w (Function.update y l t)) ∈
      Function.update (rsNested S H a).V i ((rsNested S H a).K i) l := by
    intro l y
    have := (Submodule.mem_iInf _).1 hw l
    exact (mem_axisCode_iff' _ l w).1 this y
  have hwV : w ∈ tensorCode (fun l => GoodQLTC.rsCode ((S l : Finset F) : Set F) (a l + 1)) := by
    unfold tensorCode
    rw [Submodule.mem_iInf]
    intro l
    rw [mem_axisCode_iff']
    intro y
    have := hlines l y
    by_cases hl : l = i
    · subst hl
      rw [Function.update_self] at this
      exact vanishCode_le _ _ _ this
    · rw [Function.update_of_ne hl] at this
      exact this
  have ha : ∀ l, a l < (S l).card := fun l => (hSH l).2.2.2
  obtain ⟨hdeg, hev, hPj⟩ := interp S a ha w hwV
  set P := P0 S w
  let Zp : Polynomial F := ∏ c ∈ H i, (Polynomial.X - Polynomial.C c)
  have hZmon : Zp.Monic := Polynomial.monic_prod_of_monic _ _
    (fun c _ => Polynomial.monic_X_sub_C c)
  have hZdeg : Zp.natDegree = (H i).card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C c)]
    simp
  have hZev : Polynomial.aeval (X i : MvPolynomial (Fin k) F) Zp = gridZ H i := by
    simp only [Zp, gridZ, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
  have hZ1 : Zp ≠ 1 := by
    intro h; have := hZdeg; rw [h, Polynomial.natDegree_one] at this; have := (hSH i).1; omega
  have hdiv := div_eq i Zp P
  rw [hZev] at hdiv
  -- the remainder vanishes
  obtain ⟨t0, ht0'⟩ := Finset.card_pos.mp (show 0 < (S i).card by have := ha i; omega)
  have ht0 : t0 ∈ ((S i : Finset F) : Set F) := by simpa using ht0'
  have hrem : divR i Zp P = 0 := by
    apply eq_zero_of_eval_zero_at_prod_finset _ (fun l => if l = i then H i else S l)
    · intro l
      by_cases hl : l = i
      · subst hl
        simp only [if_true]
        have := divR_degreeOf_self l Zp hZmon hZ1 P
        rwa [hZdeg] at this
      · simp only [hl, if_false]
        exact lt_of_le_of_lt ((divR_degreeOf_ne i Zp P l hl).trans (hdeg l)) (ha l)
    · intro z hz
      have hzi : z i ∈ H i := by simpa using hz i
      have hzl : ∀ l, l ≠ i → z l ∈ S l := fun l hl => by simpa [hl] using hz l
      let x : Grid S := fun l => ⟨if l = i then t0 else z l, by
        by_cases h : l = i
        · subst h; simpa using ht0'
        · simpa [h] using hzl l h⟩
      have hzx : z = Function.update (gpt S x) i (z i) := by
        funext l
        by_cases h : l = i
        · subst h; simp
        · simp [Function.update_of_ne h, gpt, x, h]
      have hPz : eval z P = 0 := by
        rw [hPj i ⟨t0, ht0⟩, hzx, eval_Pj]
        have hK := hlines i (Function.update x i ⟨t0, ht0⟩)
        rw [Function.update_self] at hK
        obtain ⟨p, hp, hpv, hpe⟩ := of_mem_vanishCode _ _ _ _ hK
        rw [lineInterp_eq S w i _ p (lt_of_lt_of_le hp (by exact_mod_cast ha i)) hpe]
        exact hpv _ hzi
      have hZz : eval z (gridZ H i) = 0 := by
        rw [gridZ, map_prod]
        exact Finset.prod_eq_zero hzi (by simp)
      have := congrArg (eval z) hdiv
      rw [map_add, map_mul, hZz, zero_mul, zero_add, hPz] at this
      exact this.symm
  rw [hrem, add_zero] at hdiv
  rw [mem_Ecert]
  refine ⟨divQ i Zp P, ⟨?_, fun l hl => ?_⟩, ?_⟩
  · have := divQ_degreeOf i Zp hZmon P i
    rw [if_pos rfl, hZdeg] at this
    exact this.trans (Nat.sub_le_sub_right (hdeg i) _)
  · have := divQ_degreeOf i Zp hZmon P l
    rw [if_neg hl] at this
    exact this.trans (hdeg l)
  · rw [← hdiv]; exact hev

end PrivPCP.L62Aux


namespace PrivPCP.R411

open GoodQLTC Classical PrivPCP.RSD MvPolynomial PrivPCP.L62Aux

variable {F : Type} [Field F] [Fintype F]
variable (Ω : Fin 2 → Finset F)

/-- the grid point with coordinates `(a, b)` -/
def mk2 (a b : F) (ha : a ∈ Ω 0) (hb : b ∈ Ω 1) : Grid Ω :=
  fun i => ⟨![a, b] i, by fin_cases i <;> simpa⟩

lemma mk2_0 (a b : F) (ha : a ∈ Ω 0) (hb : b ∈ Ω 1) : (mk2 Ω a b ha hb 0 : F) = a := rfl
lemma mk2_1 (a b : F) (ha : a ∈ Ω 0) (hb : b ∈ Ω 1) : (mk2 Ω a b ha hb 1 : F) = b := rfl

lemma mk2_eta (p : Grid Ω) : mk2 Ω (p 0) (p 1) (by simpa using (p 0).2) (by simpa using (p 1).2) = p := by
  funext i; fin_cases i <;> rfl

lemma gpt_mk2 (a b : F) (ha : a ∈ Ω 0) (hb : b ∈ Ω 1) : gpt Ω (mk2 Ω a b ha hb) = ![a, b] := by
  funext i; fin_cases i <;> rfl

lemma evGrid_mk2 (P : MvPolynomial (Fin 2) F) (a b : F) (ha : a ∈ Ω 0) (hb : b ∈ Ω 1) :
    evGrid Ω P (mk2 Ω a b ha hb) = eval ![a, b] P := by
  rw [evGrid_eq, gpt_mk2]

lemma evGrid_eq_iff (P Q : MvPolynomial (Fin 2) F) (h : evGrid Ω P = evGrid Ω Q)
    (a b : F) (ha : a ∈ Ω 0) (hb : b ∈ Ω 1) : eval ![a, b] P = eval ![a, b] Q := by
  rw [← evGrid_mk2 Ω P a b ha hb, ← evGrid_mk2 Ω Q a b ha hb, h]

/-- support of a grid word as a set of pairs -/
lemma supportCard_pairs (P : MvPolynomial (Fin 2) F) :
    supportCard (evGrid Ω P) = ((Ω 0 ×ˢ Ω 1).filter fun z => eval ![z.1, z.2] P ≠ 0).card := by
  unfold supportCard
  apply Finset.card_bij (fun p _ => ((p 0 : F), (p 1 : F)))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨by simpa using (p 0).2, by simpa using (p 1).2⟩, ?_⟩
    rw [evGrid_eq, gpt2] at hp; exact hp
  · intro p _ p' _ h
    simp only [Prod.mk.injEq] at h
    funext i; fin_cases i
    · exact Subtype.ext h.1
    · exact Subtype.ext h.2
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_product] at hz
    refine ⟨mk2 Ω z.1 z.2 hz.1.1 hz.1.2, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [evGrid_mk2]; exact hz.2

/-- line count in direction `0` is at most the number of nonzero columns -/
lemma lineCount0_le (P : MvPolynomial (Fin 2) F) :
    lineCount 0 (evGrid Ω P) ≤ ((Ω 1).filter fun b => ∃ a ∈ Ω 0, eval ![a, b] P ≠ 0).card := by
  unfold lineCount
  apply Finset.card_le_card_of_injOn (fun β => ((β ⟨1, by decide⟩ : ↥((Ω 1 : Finset F) : Set F)) : F))
  · intro β hβ
    simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
      Set.mem_setOf_eq] at hβ
    obtain ⟨p, hp, rfl⟩ := hβ
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨by simpa using (p 1).2, (p 0 : F), by simpa using (p 0).2, ?_⟩
    rw [evGrid_eq, gpt2] at hp; exact hp
  · intro β hβ β' hβ' h
    funext j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · exact absurd rfl hj
    · exact Subtype.ext h

lemma lineCount1_le (P : MvPolynomial (Fin 2) F) :
    lineCount 1 (evGrid Ω P) ≤ ((Ω 0).filter fun a => ∃ b ∈ Ω 1, eval ![a, b] P ≠ 0).card := by
  unfold lineCount
  apply Finset.card_le_card_of_injOn (fun β => ((β ⟨0, by decide⟩ : ↥((Ω 0 : Finset F) : Set F)) : F))
  · intro β hβ
    simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
      Set.mem_setOf_eq] at hβ
    obtain ⟨p, hp, rfl⟩ := hβ
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨by simpa using (p 0).2, (p 1 : F), by simpa using (p 1).2, ?_⟩
    rw [evGrid_eq, gpt2] at hp; exact hp
  · intro β hβ β' hβ' h
    funext j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · exact Subtype.ext h
    · exact absurd rfl hj

end PrivPCP.R411


namespace PrivPCP.R411

open GoodQLTC Classical PrivPCP.RSD MvPolynomial PrivPCP.L62Aux

variable {F : Type} [Field F] [Fintype F]
variable (Ω : Fin 2 → Finset F)

lemma lineCount0_le_card (z : Grid Ω → F) : lineCount 0 z ≤ (Ω 1).card := by
  have hz : z = evGrid Ω (P0 Ω z) := (evGrid_P0 Ω z).symm
  rw [hz]
  exact (lineCount0_le Ω _).trans (Finset.card_filter_le _ _)

lemma lineCount1_le_card (z : Grid Ω → F) : lineCount 1 z ≤ (Ω 0).card := by
  have hz : z = evGrid Ω (P0 Ω z) := (evGrid_P0 Ω z).symm
  rw [hz]
  exact (lineCount1_le Ω _).trans (Finset.card_filter_le _ _)

/-- decomposition of a member of the sum of axis codes -/
lemma decomp2 (C : ∀ i, Submodule F (↥((Ω i : Finset F) : Set F) → F)) (x : Grid Ω → F)
    (hx : x ∈ ⨆ i, axisCode C i) : ∃ y : Fin 2 → Grid Ω → F, (∀ i, y i ∈ axisCode C i) ∧ x = ∑ i, y i := by
  refine Submodule.iSup_induction _ (motive := fun x => ∃ y : Fin 2 → Grid Ω → F,
    (∀ i, y i ∈ axisCode C i) ∧ x = ∑ i, y i) hx ?_ ?_ ?_
  · intro i z hz
    refine ⟨Pi.single i z, fun j => ?_, ?_⟩
    · by_cases h : j = i
      · subst h; simpa using hz
      · simp [Pi.single_apply, h]
    · rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp
  · exact ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
  · rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, fun i => Submodule.add_mem _ (hf i) (hg i), by
      rw [← Finset.sum_add_distrib]; rfl⟩

/-- a grid word all of whose lines in direction `i` are low degree polynomials -/
lemma interp_dir (t : Fin 2 → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ (Ω i).card) (i : Fin 2) (z : Grid Ω → F)
    (hz : z ∈ axisCode (fun i => rsCode ((Ω i : Finset F) : Set F) (t i)) i) :
    ∃ P : MvPolynomial (Fin 2) F, evGrid Ω P = z ∧ P.degreeOf i ≤ t i - 1 ∧
      ∀ j, j ≠ i → P.degreeOf j ≤ (Ω j).card - 1 := by
  let a : Fin 2 → ℕ := fun j => if j = i then t i - 1 else (Ω j).card - 1
  have hS : ∀ j, 0 < (Ω j).card := fun j => by have := ht j; omega
  have ha : ∀ j, a j < (Ω j).card := by
    intro j; simp only [a]; split_ifs with h
    · subst h; have := ht j; omega
    · have := hS j; omega
  have hz' : z ∈ tensorCode (fun l => rsCode ((Ω l : Finset F) : Set F) (a l + 1)) := by
    unfold tensorCode
    rw [Submodule.mem_iInf]
    intro l
    by_cases hl : l = i
    · subst hl
      have : a l + 1 = t l := by simp only [a, if_pos rfl]; have := ht l; omega
      rw [mem_axisCode_iff'] at hz ⊢
      intro b
      simp only [this]
      exact hz b
    · rw [mem_axisCode_iff']
      intro b
      have : a l + 1 = (Ω l).card := by simp only [a, if_neg hl]; have := hS l; omega
      rw [this]
      exact rs_full (Ω l) _
  obtain ⟨hdeg, hev, -⟩ := interp Ω a ha z hz'
  refine ⟨P0 Ω z, hev, ?_, fun j hj => ?_⟩
  · have := hdeg i; simpa [a] using this
  · have := hdeg j; simpa [a, hj] using this

end PrivPCP.R411


namespace PrivPCP.R411

open GoodQLTC Classical PrivPCP.RSD MvPolynomial PrivPCP.L62Aux

variable {F : Type} [Field F] [Fintype F]
variable (Ω : Fin 2 → Finset F)

lemma fin2_eq (z : Fin 2 → F) : ![z 0, z 1] = z := by funext i; fin_cases i <;> rfl

lemma exists_nonzero_point (E : MvPolynomial (Fin 2) F) (hE : E ≠ 0)
    (hd : ∀ i, E.degreeOf i < Fintype.card F) : ∃ z : Fin 2 → F, eval z E ≠ 0 := by
  by_contra h
  push Not at h
  exact hE (eq_zero_of_eval_zero_at_prod_finset E (fun _ => Finset.univ) (by simpa using hd)
    (fun x _ => h x))

lemma card_le_roots (p : Polynomial F) (hp : p ≠ 0) (s : Finset F) (hs : ∀ x ∈ s, p.eval x = 0) :
    s.card ≤ p.natDegree := by
  have h1 : s ⊆ p.roots.toFinset := by
    intro x hx; rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]; exact hs x hx
  exact (Finset.card_le_card h1).trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))

/-- number of nonzeros of a nonzero low-degree polynomial on a set -/
lemma card_nonzero_ge (p : Polynomial F) (hp : p ≠ 0) (s : Finset F) :
    s.card ≤ (s.filter fun x => p.eval x ≠ 0).card + p.natDegree := by
  have := card_le_roots p hp (s.filter fun x => p.eval x = 0) (fun x hx => (Finset.mem_filter.1 hx).2)
  have h2 := Finset.card_filter_add_card_filter_not (s := s) (fun x => p.eval x ≠ 0)
  simp only [not_not] at h2
  omega

end PrivPCP.R411


namespace PrivPCP.R411

open GoodQLTC Classical PrivPCP.RSD MvPolynomial PrivPCP.L62Aux

variable {F : Type} [Field F] [Fintype F]
variable (Ω : Fin 2 → Finset F)

noncomputable def Jset (G : MvPolynomial (Fin 2) F) : Finset F :=
  (Ω 1).filter fun b => ∃ a ∈ Ω 0, eval ![a, b] G ≠ 0
noncomputable def Iset (G : MvPolynomial (Fin 2) F) : Finset F :=
  (Ω 0).filter fun a => ∃ b ∈ Ω 1, eval ![a, b] G ≠ 0
noncomputable def Wset (G : MvPolynomial (Fin 2) F) : Finset (F × F) :=
  (Ω 0 ×ˢ Ω 1).filter fun z => eval ![z.1, z.2] G ≠ 0

lemma evGrid_mem_axis (t : Fin 2 → ℕ) (i : Fin 2) (P : MvPolynomial (Fin 2) F)
    (h : P.degreeOf i < t i) :
    evGrid Ω P ∈ axisCode (fun i => rsCode ((Ω i : Finset F) : Set F) (t i)) i := by
  rw [mem_axisCode_iff']
  intro b
  refine ⟨lineRestr P i (gpt Ω b), ?_, ?_⟩
  · rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast lt_of_le_of_lt (natDegree_lineRestr _ _ _) h)
  · funext s
    simp only [evalOn, LinearMap.coe_mk, AddHom.coe_mk]
    rw [line_eval]

lemma col_count (E G : MvPolynomial (Fin 2) F) (d : ℕ) (α0 : F) (hα0 : rowP α0 E ≠ 0)
    (hEG : ∀ a ∈ Ω 0, ∀ b ∈ Ω 1, eval ![a, b] E * eval ![a, b] G = 0)
    (hG : G.degreeOf 0 ≤ d) (hd : E.degreeOf 0 + d < (Ω 0).card) :
    (Jset Ω G).card ≤ E.degreeOf 1 := by
  refine le_trans ?_ (natDegree_rowP α0 E)
  apply card_le_roots _ hα0
  intro b hb
  simp only [Jset, Finset.mem_filter] at hb
  obtain ⟨hbΩ, a, ha, hne⟩ := hb
  rw [eval_rowP]
  have hcol : colP b E = 0 := by
    by_contra hc
    have hG0 : colP b G ≠ 0 := by
      intro h0; apply hne; rw [← eval_colP, h0, Polynomial.eval_zero]
    have h1 := card_nonzero_ge (colP b G) hG0 (Ω 0)
    have h2 : ((Ω 0).filter fun x => (colP b G).eval x ≠ 0).card ≤ (colP b E).natDegree := by
      apply card_le_roots _ hc
      intro x hx
      simp only [Finset.mem_filter] at hx
      have := hEG x hx.1 b hbΩ
      rw [eval_colP] at hx ⊢
      exact (mul_eq_zero.1 this).resolve_right hx.2
    have h3 := natDegree_colP b E
    have h4 := natDegree_colP b G
    omega
  rw [← eval_colP, hcol, Polynomial.eval_zero]

lemma row_count (E G : MvPolynomial (Fin 2) F) (d : ℕ) (β0 : F) (hβ0 : colP β0 E ≠ 0)
    (hEG : ∀ a ∈ Ω 0, ∀ b ∈ Ω 1, eval ![a, b] E * eval ![a, b] G = 0)
    (hG : G.degreeOf 1 ≤ d) (hd : E.degreeOf 1 + d < (Ω 1).card) :
    (Iset Ω G).card ≤ E.degreeOf 0 := by
  refine le_trans ?_ (natDegree_colP β0 E)
  apply card_le_roots _ hβ0
  intro a ha
  simp only [Iset, Finset.mem_filter] at ha
  obtain ⟨haΩ, b, hb, hne⟩ := ha
  rw [eval_colP]
  have hrow : rowP a E = 0 := by
    by_contra hc
    have hG0 : rowP a G ≠ 0 := by
      intro h0; apply hne; rw [← eval_rowP, h0, Polynomial.eval_zero]
    have h1 := card_nonzero_ge (rowP a G) hG0 (Ω 1)
    have h2 : ((Ω 1).filter fun y => (rowP a G).eval y ≠ 0).card ≤ (rowP a E).natDegree := by
      apply card_le_roots _ hc
      intro y hy
      simp only [Finset.mem_filter] at hy
      have := hEG a haΩ y hy.1
      rw [eval_rowP] at hy ⊢
      exact (mul_eq_zero.1 this).resolve_right hy.2
    have h3 := natDegree_rowP a E
    have h4 := natDegree_rowP a G
    omega
  rw [← eval_rowP, hrow, Polynomial.eval_zero]

lemma count_J (G0 G1 : MvPolynomial (Fin 2) F) (d h : ℕ) (hG : G0.degreeOf 0 ≤ d)
    (hd : h + 1 + d ≤ (Ω 0).card) :
    (Jset Ω G0).card * (h + 1) ≤ (Wset Ω (G0 + G1)).card + (Jset Ω G0).card * (Iset Ω G1).card := by
  set J := Jset Ω G0
  set I := Iset Ω G1
  set p : F × F → Prop := fun z => eval ![z.1, z.2] G0 ≠ 0 ∧ z.1 ∉ I with hp
  have hsub : (Ω 0 ×ˢ J).filter p ⊆ Wset Ω (G0 + G1) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_product, p, J, Jset, Wset] at hz ⊢
    obtain ⟨⟨h1, h2, -⟩, h3, h4⟩ := hz
    refine ⟨⟨h1, h2⟩, ?_⟩
    have : eval ![z.1, z.2] G1 = 0 := by
      by_contra hc; exact h4 (Finset.mem_filter.2 ⟨h1, z.2, h2, hc⟩)
    rw [map_add, this, add_zero]; exact h3
  have hcard : ((Ω 0 ×ˢ J).filter p).card = ∑ b ∈ J, ((Ω 0).filter fun a => p (a, b)).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.card_filter]
  have hper : ∀ b ∈ J, h + 1 ≤ ((Ω 0).filter fun a => p (a, b)).card + I.card := by
    intro b hb
    simp only [J, Jset, Finset.mem_filter] at hb
    obtain ⟨hbΩ, a, ha, hne⟩ := hb
    have hc : colP b G0 ≠ 0 := by
      intro h0; apply hne; rw [← eval_colP, h0, Polynomial.eval_zero]
    have h1 := card_nonzero_ge (colP b G0) hc (Ω 0)
    have h2 := (natDegree_colP b G0).trans hG
    have h3 : ((Ω 0).filter fun x => (colP b G0).eval x ≠ 0) ⊆
        ((Ω 0).filter fun a => p (a, b)) ∪ I := by
      intro x hx
      simp only [Finset.mem_filter, eval_colP] at hx
      by_cases hxI : x ∈ I
      · exact Finset.mem_union_right _ hxI
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx.1, hx.2, hxI⟩)
    have h4 := (Finset.card_le_card h3).trans (Finset.card_union_le _ _)
    omega
  calc J.card * (h + 1) = ∑ b ∈ J, (h + 1) := by simp
    _ ≤ ∑ b ∈ J, (((Ω 0).filter fun a => p (a, b)).card + I.card) := Finset.sum_le_sum hper
    _ = ((Ω 0 ×ˢ J).filter p).card + J.card * I.card := by
        rw [Finset.sum_add_distrib, hcard]; simp
    _ ≤ _ := by have := Finset.card_le_card hsub; omega

lemma count_I (G0 G1 : MvPolynomial (Fin 2) F) (d h : ℕ) (hG : G1.degreeOf 1 ≤ d)
    (hd : h + 1 + d ≤ (Ω 1).card) :
    (Iset Ω G1).card * (h + 1) ≤ (Wset Ω (G0 + G1)).card + (Iset Ω G1).card * (Jset Ω G0).card := by
  set J := Jset Ω G0
  set I := Iset Ω G1
  set p : F × F → Prop := fun z => eval ![z.1, z.2] G1 ≠ 0 ∧ z.2 ∉ J with hp
  have hsub : (I ×ˢ Ω 1).filter p ⊆ Wset Ω (G0 + G1) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_product, p, I, Iset, Wset] at hz ⊢
    obtain ⟨⟨⟨h1, -⟩, h2⟩, h3, h4⟩ := hz
    refine ⟨⟨h1, h2⟩, ?_⟩
    have : eval ![z.1, z.2] G0 = 0 := by
      by_contra hc; exact h4 (Finset.mem_filter.2 ⟨h2, z.1, h1, hc⟩)
    rw [map_add, this, zero_add]; exact h3
  have hcard : ((I ×ˢ Ω 1).filter p).card = ∑ a ∈ I, ((Ω 1).filter fun b => p (a, b)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
  have hper : ∀ a ∈ I, h + 1 ≤ ((Ω 1).filter fun b => p (a, b)).card + J.card := by
    intro a ha
    simp only [I, Iset, Finset.mem_filter] at ha
    obtain ⟨haΩ, b, hb, hne⟩ := ha
    have hc : rowP a G1 ≠ 0 := by
      intro h0; apply hne; rw [← eval_rowP, h0, Polynomial.eval_zero]
    have h1 := card_nonzero_ge (rowP a G1) hc (Ω 1)
    have h2 := (natDegree_rowP a G1).trans hG
    have h3 : ((Ω 1).filter fun y => (rowP a G1).eval y ≠ 0) ⊆
        ((Ω 1).filter fun b => p (a, b)) ∪ J := by
      intro y hy
      simp only [Finset.mem_filter, eval_rowP] at hy
      by_cases hyJ : y ∈ J
      · exact Finset.mem_union_right _ hyJ
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hy.1, hy.2, hyJ⟩)
    have h4 := (Finset.card_le_card h3).trans (Finset.card_union_le _ _)
    omega
  calc I.card * (h + 1) = ∑ a ∈ I, (h + 1) := by simp
    _ ≤ ∑ a ∈ I, (((Ω 1).filter fun b => p (a, b)).card + J.card) := Finset.sum_le_sum hper
    _ = ((I ×ˢ Ω 1).filter p).card + I.card * J.card := by
        rw [Finset.sum_add_distrib, hcard]; simp
    _ ≤ _ := by have := Finset.card_le_card hsub; omega

end PrivPCP.R411


namespace PrivPCP.R411

open GoodQLTC Classical PrivPCP.RSD MvPolynomial PrivPCP.L62Aux

variable {F : Type} [Field F] [Fintype F]
variable (Ω : Fin 2 → Finset F)

lemma final_arith (ρ n0 n1 l0 l1 j i h w τ : ℝ) (hρ : 0 < ρ) (hn0 : 0 ≤ n0) (hn1 : 0 ≤ n1)
    (hl0 : l0 ≤ j) (hl1 : l1 ≤ i) (hh : 0 < h) (hρ2 : ρ * (2 * (n0 + n1)) ≤ h) (hw : 0 ≤ w)
    (hjT : j ≤ τ) (hiT : i ≤ τ) (hτh : 2 * τ ≤ h) (cJ : j * (h + 1) ≤ w + j * i)
    (cI : i * (h + 1) ≤ w + i * j) (hj0 : 0 ≤ j) (hi0 : 0 ≤ i) :
    ρ * (n0 * l0 + n1 * l1) ≤ w := by
  have hjh : j * h ≤ 2 * w := by
    have e1 := mul_le_mul_of_nonneg_left hiT hj0
    have e2 := mul_le_mul_of_nonneg_left hτh hj0
    nlinarith
  have hih : i * h ≤ 2 * w := by
    have e1 := mul_le_mul_of_nonneg_left hjT hi0
    have e2 := mul_le_mul_of_nonneg_left hτh hi0
    nlinarith
  have e1 : n0 * l0 + n1 * l1 ≤ n0 * j + n1 * i := by
    have := mul_le_mul_of_nonneg_left hl0 hn0
    have := mul_le_mul_of_nonneg_left hl1 hn1
    linarith
  have e2 : (n0 * j + n1 * i) * h ≤ 2 * w * (n0 + n1) := by
    have := mul_le_mul_of_nonneg_left hjh hn0
    have := mul_le_mul_of_nonneg_left hih hn1
    nlinarith
  have e3 : ρ * (n0 * l0 + n1 * l1) * h ≤ w * h := by
    have a := mul_le_mul_of_nonneg_right e1 hh.le
    have b := mul_le_mul_of_nonneg_left (a.trans e2) hρ.le
    have c := mul_le_mul_of_nonneg_right hρ2 hw
    nlinarith
  exact (mul_le_mul_iff_of_pos_right hh).1 e3

set_option maxHeartbeats 1000000 in
theorem core (t : Fin 2 → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i < (Ω i).card) (τ ρ : ℝ) (hρ : 0 < ρ)
    (hτ0 : 0 ≤ τ)
    (hτh : 2 * τ ≤ ((min ((Ω 0).card - t 0) ((Ω 1).card - t 1) : ℕ) : ℝ))
    (hρ1 : ρ * (2 * (((Ω 0).card : ℝ) * (Ω 1).card)) ≤ τ ^ 2)
    (hρ2 : ρ * (2 * (((Ω 0).card : ℝ) + (Ω 1).card)) ≤
      ((min ((Ω 0).card - t 0) ((Ω 1).card - t 1) : ℕ) : ℝ))
    (H : ∀ E P : MvPolynomial (Fin 2) F, E ≠ 0 → (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ →
      P.degreeOf 0 < t 0 + E.degreeOf 0 → P.degreeOf 1 < t 1 + E.degreeOf 1 →
      (∀ α ∈ Ω 0, ∃ R, rowP α P = rowP α E * R) → (∀ β ∈ Ω 1, ∃ R, colP β P = colP β E * R) →
      ∃ Q, P = E * Q ∧ Q.degreeOf 0 < t 0 ∧ Q.degreeOf 1 < t 1) :
    IsProductExpanding ρ (fun i => rsCode ((Ω i : Finset F) : Set F) (t i)) := by
  refine ⟨hρ, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := decomp2 Ω (fun i => rsCode ((Ω i : Finset F) : Set F) (t i)) x hx
  set w := supportCard x with hw
  set T := Nat.sqrt w with hT
  have hTw : T * T ≤ w := Nat.sqrt_le w
  have hwT : w < (T + 1) * (T + 1) := Nat.lt_succ_sqrt w
  clear_value T
  set h := min ((Ω 0).card - t 0) ((Ω 1).card - t 1) with hh
  have hcard : ∀ i, Fintype.card ↥((Ω i : Finset F) : Set F) = (Ω i).card := fun i => by simp
  have hxp : ∀ p, x p = y 0 p + y 1 p := by
    intro p; rw [hxy, Finset.sum_apply, Fin.sum_univ_two]
  by_cases hbig : τ < T
  · refine ⟨y, hy, hxy, ?_⟩
    rw [Fin.sum_univ_two, hcard, hcard]
    have l0 : (lineCount 0 (y 0) : ℝ) ≤ (Ω 1).card := by exact_mod_cast lineCount0_le_card Ω _
    have l1 : (lineCount 1 (y 1) : ℝ) ≤ (Ω 0).card := by exact_mod_cast lineCount1_le_card Ω _
    have hwr : (T : ℝ) * T ≤ w := by exact_mod_cast hTw
    have h2 : τ ^ 2 ≤ (T : ℝ) * T := by nlinarith
    have hn0 : (0 : ℝ) ≤ (Ω 0).card := by positivity
    have hn1 : (0 : ℝ) ≤ (Ω 1).card := by positivity
    calc ρ * (((Ω 0).card : ℝ) * lineCount 0 (y 0) + (Ω 1).card * lineCount 1 (y 1))
        ≤ ρ * (2 * (((Ω 0).card : ℝ) * (Ω 1).card)) := by
          apply mul_le_mul_of_nonneg_left _ hρ.le
          nlinarith [mul_le_mul_of_nonneg_left l0 hn0, mul_le_mul_of_nonneg_left l1 hn1]
      _ ≤ w := by linarith
  push Not at hbig
  have hhn : ∀ i, h ≤ (Ω i).card - t i := by
    intro i; fin_cases i
    · exact Nat.min_le_left _ _
    · exact Nat.min_le_right _ _
  have h2T : 2 * T ≤ h := by
    have : ((2 * T : ℕ) : ℝ) ≤ h := by push_cast; linarith
    exact_mod_cast this
  have ht0 := ht 0
  have ht1 := ht 1
  have hh0 := hhn 0
  have hh1 := hhn 1
  clear_value h
  -- the vanishing polynomial
  set Sup : Finset (F × F) := (Finset.univ.filter fun p : Grid Ω => x p ≠ 0).image
    fun p => ((p 0 : F), (p 1 : F)) with hSupdef
  have hSup : Sup.card < (T + 1) * (T + 1) := lt_of_le_of_lt Finset.card_image_le hwT
  obtain ⟨E, hE0, hEX, hEY, hEv⟩ := exists_vanishing Sup T hSup
  have hEz : ∀ p : Grid Ω, x p ≠ 0 → eval (gpt Ω p) E = 0 := by
    intro p hp
    rw [gpt2 Ω p]
    exact hEv ((p 0 : F), (p 1 : F)) (Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩, rfl⟩)
  have ht' : ∀ i, 1 ≤ t i ∧ t i ≤ (Ω i).card := fun i => ⟨(ht i).1, (ht i).2.le⟩
  obtain ⟨A, hA, hA0, -⟩ := interp_dir Ω t ht' 0 (y 0) (hy 0)
  obtain ⟨B, hB, hB1, -⟩ := interp_dir Ω t ht' 1 (y 1) (hy 1)
  have hzB : evGrid Ω (E * A) = evGrid Ω (E * -B) := by
    funext p
    rw [evGrid_eq, evGrid_eq, map_mul, map_mul, map_neg]
    by_cases hx0 : x p = 0
    · have h1 := hxp p
      rw [hx0, ← hA, ← hB, evGrid_eq, evGrid_eq] at h1
      have : eval (gpt Ω p) A = - eval (gpt Ω p) B := by linear_combination -h1
      rw [this]
    · rw [hEz p hx0, zero_mul, zero_mul]
  set a : Fin 2 → ℕ := ![E.degreeOf 0 + t 0 - 1, E.degreeOf 1 + t 1 - 1] with hadef
  have ha : ∀ l, a l < (Ω l).card := by
    intro l; fin_cases l
    · simp [a]; omega
    · simp [a]; omega
  have hdEA : (E * A).degreeOf 0 ≤ E.degreeOf 0 + t 0 - 1 := by
    have := degreeOf_mul_le 0 E A; omega
  have hdEB : (E * -B).degreeOf 1 ≤ E.degreeOf 1 + t 1 - 1 := by
    have := degreeOf_mul_le 1 E (-B); rw [degreeOf_neg] at this; omega
  have hzT : evGrid Ω (E * A) ∈
      tensorCode (fun l => rsCode ((Ω l : Finset F) : Set F) (a l + 1)) := by
    unfold tensorCode; rw [Submodule.mem_iInf]; intro l; fin_cases l
    · apply evGrid_mem_axis Ω (fun l => a l + 1) 0
      show _ < a 0 + 1
      have : a 0 = E.degreeOf 0 + t 0 - 1 := rfl
      omega
    · rw [hzB]; apply evGrid_mem_axis Ω (fun l => a l + 1) 1
      show _ < a 1 + 1
      have : a 1 = E.degreeOf 1 + t 1 - 1 := rfl
      omega
  obtain ⟨hdegP, hevP, -⟩ := interp Ω a ha _ hzT
  set P := P0 Ω (evGrid Ω (E * A)) with hPdef
  have hrow : ∀ α ∈ Ω 0, ∃ R, rowP α P = rowP α E * R := by
    intro α hα
    refine ⟨rowP α (-B), ?_⟩
    rw [← rowP_mul]
    apply poly_eq_on (Ω 1)
    · exact lt_of_le_of_lt (natDegree_rowP _ _) (lt_of_le_of_lt (hdegP 1) (ha 1))
    · refine lt_of_le_of_lt (natDegree_rowP _ _) ?_
      have := ha 1; simp [a] at this; omega
    · intro b hb
      rw [eval_rowP, eval_rowP, ← evGrid_mk2 Ω _ α b hα hb, ← evGrid_mk2 Ω _ α b hα hb, hevP, hzB]
  have hcol : ∀ β ∈ Ω 1, ∃ R, colP β P = colP β E * R := by
    intro β hβ
    refine ⟨colP β A, ?_⟩
    rw [← colP_mul]
    apply poly_eq_on (Ω 0)
    · exact lt_of_le_of_lt (natDegree_colP _ _) (lt_of_le_of_lt (hdegP 0) (ha 0))
    · refine lt_of_le_of_lt (natDegree_colP _ _) ?_
      have := ha 0; simp [a] at this; omega
    · intro b hb
      rw [eval_colP, eval_colP, ← evGrid_mk2 Ω _ b β hb hβ, ← evGrid_mk2 Ω _ b β hb hβ, hevP]
  have hmax : (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ := by
    refine max_le ?_ ?_
    · exact le_trans (by exact_mod_cast hEX) hbig
    · exact le_trans (by exact_mod_cast hEY) hbig
  have hP0 : P.degreeOf 0 < t 0 + E.degreeOf 0 := by
    have := hdegP 0; simp [a] at this; omega
  have hP1 : P.degreeOf 1 < t 1 + E.degreeOf 1 := by
    have := hdegP 1; simp [a] at this; omega
  obtain ⟨Q, hPQ, hQ0, hQ1⟩ := H E P hE0 hmax hP0 hP1 hrow hcol
  set G0 := A - Q
  set G1 := B + Q
  have hG0 : G0.degreeOf 0 ≤ t 0 - 1 := by
    have : G0.degreeOf 0 ≤ max (A.degreeOf 0) (Q.degreeOf 0) := degreeOf_sub_le 0 A Q
    have := max_le hA0 (show Q.degreeOf 0 ≤ t 0 - 1 by omega)
    omega
  have hG1 : G1.degreeOf 1 ≤ t 1 - 1 := by
    have : G1.degreeOf 1 ≤ max (B.degreeOf 1) (Q.degreeOf 1) := degreeOf_add_le 1 B Q
    have := max_le hB1 (show Q.degreeOf 1 ≤ t 1 - 1 by omega)
    omega
  -- `E` annihilates both new pieces on the grid
  have hEP : ∀ a' ∈ Ω 0, ∀ b ∈ Ω 1, eval ![a', b] E * eval ![a', b] A = eval ![a', b] E * eval ![a', b] Q := by
    intro a' ha' b hb
    have := congrFun hevP (mk2 Ω a' b ha' hb)
    rw [evGrid_mk2, evGrid_mk2, hPQ, map_mul, map_mul] at this
    exact this.symm
  have hEP' : ∀ a' ∈ Ω 0, ∀ b ∈ Ω 1, -(eval ![a', b] E * eval ![a', b] B) = eval ![a', b] E * eval ![a', b] Q := by
    intro a' ha' b hb
    have := congrFun hevP (mk2 Ω a' b ha' hb)
    rw [hzB, evGrid_mk2, evGrid_mk2, hPQ, map_mul, map_mul, map_neg] at this
    linear_combination -this
  have hEG0 : ∀ a' ∈ Ω 0, ∀ b ∈ Ω 1, eval ![a', b] E * eval ![a', b] G0 = 0 := by
    intro a' ha' b hb
    have := hEP a' ha' b hb
    simp only [G0, map_sub]; linear_combination this
  have hEG1 : ∀ a' ∈ Ω 0, ∀ b ∈ Ω 1, eval ![a', b] E * eval ![a', b] G1 = 0 := by
    intro a' ha' b hb
    have := hEP' a' ha' b hb
    simp only [G1, map_add]; linear_combination -this
  -- a nonzero value of `E`
  have hdegF : ∀ i, E.degreeOf i < Fintype.card F := by
    have c0 := Finset.card_le_univ (Ω 0)
    intro i; fin_cases i
    · simp; omega
    · simp; omega
  obtain ⟨z, hz⟩ := exists_nonzero_point E hE0 hdegF
  have hrz : rowP (z 0) E ≠ 0 := by
    intro h0; apply hz; rw [← fin2_eq z, ← eval_rowP, h0, Polynomial.eval_zero]
  have hcz : colP (z 1) E ≠ 0 := by
    intro h0; apply hz; rw [← fin2_eq z, ← eval_colP, h0, Polynomial.eval_zero]
  have hJ := col_count Ω E G0 (t 0 - 1) (z 0) hrz hEG0 hG0 (by omega)
  have hI := row_count Ω E G1 (t 1 - 1) (z 1) hcz hEG1 hG1 (by omega)
  have cJ := count_J Ω G0 G1 (t 0 - 1) h hG0 (by omega)
  have cI := count_I Ω G0 G1 (t 1 - 1) h hG1 (by omega)
  have hxG : x = evGrid Ω (G0 + G1) := by
    funext p
    rw [hxp p, ← hA, ← hB, evGrid_eq, evGrid_eq, evGrid_eq]
    simp only [G0, G1, map_add, map_sub]; ring
  have hW : (Wset Ω (G0 + G1)).card = w := by
    rw [hw, hxG, supportCard_pairs]; rfl
  refine ⟨![evGrid Ω G0, evGrid Ω G1], ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact evGrid_mem_axis Ω t 0 G0 (by omega)
    · exact evGrid_mem_axis Ω t 1 G1 (by omega)
  · rw [Fin.sum_univ_two, hxG]
    funext p
    simp [evGrid_eq]
  · rw [Fin.sum_univ_two, hcard, hcard]
    have l0 : lineCount 0 (evGrid Ω G0) ≤ (Jset Ω G0).card := lineCount0_le Ω G0
    have l1 : lineCount 1 (evGrid Ω G1) ≤ (Iset Ω G1).card := lineCount1_le Ω G1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hW] at cJ cI
    clear_value w
    set j := (Jset Ω G0).card
    set i := (Iset Ω G1).card
    have hjT : (j : ℝ) ≤ τ := le_trans (by exact_mod_cast hJ.trans hEY) hbig
    have hiT : (i : ℝ) ≤ τ := le_trans (by exact_mod_cast hI.trans hEX) hbig
    have cJr : (j : ℝ) * (h + 1) ≤ w + j * i := by exact_mod_cast cJ
    have cIr : (i : ℝ) * (h + 1) ≤ w + i * j := by exact_mod_cast cI
    have hhpos : (0 : ℝ) < h := by
      have : 1 ≤ h := by omega
      exact_mod_cast this
    have l0r : (lineCount 0 (evGrid Ω G0) : ℝ) ≤ j := by exact_mod_cast l0
    have l1r : (lineCount 1 (evGrid Ω G1) : ℝ) ≤ i := by exact_mod_cast l1
    exact final_arith ρ _ _ _ _ j i h w τ hρ (by positivity) (by positivity) l0r l1r hhpos hρ2
      (by positivity) hjT hiT hτh cJr cIr (by positivity) (by positivity)

end PrivPCP.R411


namespace PrivPCP.R411

open GoodQLTC Classical MvPolynomial

lemma card_subgroupSet {q : ℕ} [Fact q.Prime] (S : Subgroup (ZMod q)ˣ) :
    (subgroupSet S).card = Nat.card S := by
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  symm
  apply Finset.card_bij (fun (u : S) _ => ((u : (ZMod q)ˣ) : ZMod q))
  · intro u _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, u, u.2, rfl⟩
  · intro u _ v _ h
    exact Subtype.ext (Units.ext h)
  · intro x hx
    obtain ⟨-, u, hu, rfl⟩ := Finset.mem_filter.1 hx
    exact ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩

lemma arith (c1 ε K n0 n1 h m : ℝ) (hc1 : 0 < c1) (hc1' : c1 ≤ 1 / 2) (hε : 0 < ε) (hε1 : ε < 1)
    (hK : 1 ≤ K) (hn0 : 0 < n0) (hn1 : 0 < n1) (hm : 0 < m) (hmh : ε * m ≤ h)
    (hm0 : n0 ≤ K * m) (hm1 : n1 ≤ K * m) (hNm : n0 * n1 ≤ K * m ^ 2)
    (hh0 : h ≤ n0) (hh1 : h ≤ n1) :
    2 * (c1 * h ^ 3 / (n0 * n1)) ≤ h ∧
    c1 ^ 2 / 2 * ε ^ 6 / K ^ 3 * (2 * (n0 * n1)) ≤ (c1 * h ^ 3 / (n0 * n1)) ^ 2 ∧
    c1 ^ 2 / 2 * ε ^ 6 / K ^ 3 * (2 * (n0 + n1)) ≤ h := by
  have hN : 0 < n0 * n1 := mul_pos hn0 hn1
  have hhpos : 0 < h := lt_of_lt_of_le (mul_pos hε hm) hmh
  have hK3 : K ≤ K ^ 3 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 3 := pow_le_pow_right₀ hK (by norm_num)
  have hK3p : 0 < K ^ 3 := by positivity
  have hhN : h * h ≤ n0 * n1 := mul_le_mul hh0 hh1 hhpos.le hn0.le
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_div_assoc', div_le_iff₀ hN]
    have : h ^ 3 = h * (h * h) := by ring
    rw [this]
    have h1 : h * (h * h) ≤ h * (n0 * n1) := mul_le_mul_of_nonneg_left hhN hhpos.le
    have h2 : 2 * c1 * (h * (h * h)) ≤ 1 * (h * (h * h)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  · have k1 : ε ^ 2 * (n0 * n1) ≤ K * h ^ 2 := by
      have a1 : ε * m * (ε * m) ≤ h * h := mul_le_mul hmh hmh (by positivity) hhpos.le
      have a3 : ε ^ 2 * (n0 * n1) ≤ ε ^ 2 * (K * m ^ 2) :=
        mul_le_mul_of_nonneg_left hNm (by positivity)
      have a4 : K * (ε * m * (ε * m)) ≤ K * (h * h) := mul_le_mul_of_nonneg_left a1 (by linarith)
      nlinarith
    have k3 : (ε ^ 2 * (n0 * n1)) ^ 3 ≤ (K * h ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) k1 3
    rw [div_pow, mul_pow]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hK3p (by positivity)]
    have e : (c1 ^ 2 / 2 * ε ^ 6 * (2 * (n0 * n1))) * (n0 * n1) ^ 2 = c1 ^ 2 * (ε ^ 2 * (n0 * n1)) ^ 3 := by ring
    have e2 : c1 ^ 2 * (h ^ 3) ^ 2 * K ^ 3 = c1 ^ 2 * (K * h ^ 2) ^ 3 := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left k3 (by positivity)
  · have hε6 : ε ^ 6 ≤ ε := by
      calc ε ^ 6 ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1.le (by norm_num)
        _ = ε := pow_one ε
    have hc2 : c1 ^ 2 ≤ 1 / 4 := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hK3p]
    have s1 : c1 ^ 2 * ε ^ 6 ≤ 1 / 4 * ε := mul_le_mul hc2 hε6 (by positivity) (by norm_num)
    have s2 : c1 ^ 2 / 2 * ε ^ 6 * (2 * (n0 + n1)) = (c1 ^ 2 * ε ^ 6) * (n0 + n1) := by ring
    have s3 : (c1 ^ 2 * ε ^ 6) * (n0 + n1) ≤ 1 / 4 * ε * (n0 + n1) :=
      mul_le_mul_of_nonneg_right s1 (by positivity)
    have s4 : ε * (n0 + n1) ≤ ε * (2 * K * m) := mul_le_mul_of_nonneg_left (by linarith) hε.le
    have s5 : K * (ε * m) ≤ K * h := mul_le_mul_of_nonneg_left hmh (by linarith)
    have s6 : K * h ≤ h * K ^ 3 := by nlinarith
    nlinarith

end PrivPCP.R411

open PrivPCP PrivPCP.R411 GoodQLTC Classical MvPolynomial in
theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ K : ℝ, 1 ≤ K →
    ∃ ρ : ℝ, c * ε ^ 6 / K ^ 3 ≤ ρ ∧ ρ ≤ 1 ∧ PunctRSPE 2 ε K ρ := by
  obtain ⟨c0, hc0, H413⟩ := PrivPCP.lemma_4_13_kpos
  set c1 := min c0 (1 / 2) with hc1def
  have hc1 : 0 < c1 := lt_min hc0 (by norm_num)
  have hc1' : c1 ≤ 1 / 2 := min_le_right _ _
  have hc10 : c1 ≤ c0 := min_le_left _ _
  refine ⟨c1 ^ 2 / 2, by positivity, fun ε hε hε1 K hK => ⟨c1 ^ 2 / 2 * ε ^ 6 / K ^ 3, le_rfl, ?_, ?_⟩⟩
  · have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
    rw [div_le_one (by positivity)]
    have h6 : ε ^ 6 ≤ 1 := pow_le_one₀ hε.le hε1.le
    have hc2 : c1 ^ 2 / 2 ≤ 1 := by nlinarith
    have := mul_le_mul hc2 h6 (by positivity) (by norm_num)
    linarith
  intro q _ S hcop hbal t ht Λ
  apply pe_rescale
  have hc : ∀ i, (subgroupSet (S i)).card = Nat.card (S i) := fun i => card_subgroupSet (S i)
  have hpos : ∀ i, 0 < Nat.card (S i) := fun i => Nat.card_pos
  have htlt : ∀ i, 1 ≤ t i ∧ t i < (subgroupSet (S i)).card := by
    intro i
    refine ⟨(ht i).1, ?_⟩
    rw [hc]
    have h1 := (ht i).2
    have h2 : (0 : ℝ) < Nat.card (S i) := by exact_mod_cast hpos i
    have : (t i : ℝ) < Nat.card (S i) := by nlinarith
    exact_mod_cast this
  have ht0 := htlt 0
  have ht1 := htlt 1
  rw [hc] at ht0 ht1
  have hb10 : (Nat.card (S 1) : ℝ) ≤ K * Nat.card (S 0) := by
    have := (hbal 1 0).2
    rwa [div_le_iff₀ (by exact_mod_cast hpos 0)] at this
  have hb01 : (Nat.card (S 0) : ℝ) ≤ K * Nat.card (S 1) := by
    have := (hbal 0 1).2
    rwa [div_le_iff₀ (by exact_mod_cast hpos 1)] at this
  have hp0 : (0 : ℝ) < Nat.card (S 0) := by exact_mod_cast hpos 0
  have hp1 : (0 : ℝ) < Nat.card (S 1) := by exact_mod_cast hpos 1
  set n0 := Nat.card (S 0) with hn0def
  set n1 := Nat.card (S 1) with hn1def
  set hN := min (n0 - t 0) (n1 - t 1) with hhN
  have hcast : (hN : ℝ) = min ((n0 : ℝ) - t 0) ((n1 : ℝ) - t 1) := by
    rw [hhN, Nat.cast_min, Nat.cast_sub ht0.2.le, Nat.cast_sub ht1.2.le]
  have ha0 : ε * (n0 : ℝ) ≤ n0 - t 0 := by have := (ht 0).2; linarith
  have ha1 : ε * (n1 : ℝ) ≤ n1 - t 1 := by have := (ht 1).2; linarith
  have hhn0 : (hN : ℝ) ≤ n0 := by rw [hcast]; have := min_le_left ((n0 : ℝ) - t 0) ((n1 : ℝ) - t 1); have : (0:ℝ) ≤ t 0 := (by positivity); linarith
  have hhn1 : (hN : ℝ) ≤ n1 := by rw [hcast]; have := min_le_right ((n0 : ℝ) - t 0) ((n1 : ℝ) - t 1); have : (0:ℝ) ≤ t 1 := (by positivity); linarith
  have hK0 : (0 : ℝ) ≤ K := by linarith
  obtain ⟨m, hm, hmh, hm0, hm1, hNm⟩ : ∃ m : ℝ, 0 < m ∧ ε * m ≤ hN ∧ (n0 : ℝ) ≤ K * m ∧ (n1 : ℝ) ≤ K * m ∧
      (n0 : ℝ) * n1 ≤ K * m ^ 2 := by
    rcases le_total (n0 : ℝ) n1 with hle | hle
    · refine ⟨n0, hp0, ?_, by nlinarith, hb10, ?_⟩
      · rw [hcast]; refine le_min ha0 ?_
        have := mul_le_mul_of_nonneg_left hle hε.le; linarith
      · have := mul_le_mul_of_nonneg_left hb10 hp0.le; nlinarith
    · refine ⟨n1, hp1, ?_, hb01, by nlinarith, ?_⟩
      · rw [hcast]; refine le_min ?_ ha1
        have := mul_le_mul_of_nonneg_left hle hε.le; linarith
      · have := mul_le_mul_of_nonneg_left hb01 hp1.le; nlinarith
  obtain ⟨A1, A2, A3⟩ := arith c1 ε K n0 n1 hN m hc1 hc1' hε hε1 hK hp0 hp1 hm hmh hm0 hm1 hNm hhn0 hhn1
  have hNcast : ((n0 * n1 : ℕ) : ℝ) = (n0 : ℝ) * n1 := by push_cast; ring
  refine core (fun i => subgroupSet (S i)) t htlt (c1 * (hN : ℝ) ^ 3 / ((n0 * n1 : ℕ) : ℝ)) _
    (by positivity) (by positivity) ?_ ?_ ?_ ?_
  · show _ ≤ ((min ((subgroupSet (S 0)).card - t 0) ((subgroupSet (S 1)).card - t 1) : ℕ) : ℝ)
    rw [hc 0, hc 1, hNcast]; exact A1
  · show _ * (2 * (((subgroupSet (S 0)).card : ℝ) * (subgroupSet (S 1)).card)) ≤ _
    rw [hc 0, hc 1, hNcast]; exact A2
  · show _ * (2 * (((subgroupSet (S 0)).card : ℝ) + (subgroupSet (S 1)).card)) ≤
      ((min ((subgroupSet (S 0)).card - t 0) ((subgroupSet (S 1)).card - t 1) : ℕ) : ℝ)
    rw [hc 0, hc 1]; exact A3
  · intro E P hE hmax hP0 hP1 hrow hcol
    have hb : (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤
        c0 * (hN : ℝ) ^ 3 / ((n0 * n1 : ℕ) : ℝ) := by
      refine hmax.trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hc10 (by positivity)
    obtain ⟨-, Q, hQ⟩ := H413 q (S 0) (S 1) (hcop 0 1 (by decide)) (t 0) (t 1) (ht 0).1 (ht 1).1
      ht0.2 ht1.2 E P hE hb hP0 hP1
      (fun α hα => hrow (α : ZMod q) (Finset.mem_filter.2 ⟨Finset.mem_univ _, α, hα, rfl⟩))
      (fun β hβ => hcol (β : ZMod q) (Finset.mem_filter.2 ⟨Finset.mem_univ _, β, hβ, rfl⟩))
    exact ⟨Q, hQ⟩


