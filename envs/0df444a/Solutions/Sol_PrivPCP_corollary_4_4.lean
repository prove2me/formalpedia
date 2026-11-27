-- Prove2me | solution 1 for PrivPCP.corollary_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:16:03.445796+00:00
-- url     : https://prove2.me/submissions/26b4e23d-014d-4bc8-bd58-315f7c346c1f

import Mathlib
import Definitions.Def_PrivPCP_PunctRSPE
import Definitions.Def_PrivPCP_rsNested
import Theorems.Thm_PrivPCP_corollary_4_10


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


namespace PrivPCP.PERe

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
variable {T : κ → Type} [∀ k, Fintype (T k)]

/-- `Φ ω' i = ω' (e i)` -/
abbrev Φ : (∀ k, T k) ≃ (∀ i, T (e i)) := Equiv.piCongrLeft' T e.symm

lemma Φ_apply (ω' : ∀ k, T k) (i : ι) : Φ e ω' i = ω' (e i) := rfl

lemma Φ_update (f : ∀ k, T k) (i : ι) (x : T (e i)) :
    Φ e (Function.update f (e i) x) = Function.update (Φ e f) i x :=
  Function.piCongrLeft'_update T e.symm f i x

lemma Φsymm_update (g : ∀ i, T (e i)) (i : ι) (x : T (e i)) :
    (Φ e).symm (Function.update g i x) = Function.update ((Φ e).symm g) (e i) x :=
  Function.piCongrLeft'_symm_update T e.symm g i x

lemma Φsymm_e (a : ∀ i, T (e i)) (j : ι) : (Φ e).symm a (e j) = a j :=
  congrFun ((Φ e).apply_symm_apply a) j

lemma card_image_eq {α β γ δ : Type} {_ : DecidableEq γ} {_ : DecidableEq δ} (s : Finset α) (t : Finset β)
    (φ : α → β) (hφ : Set.BijOn φ s t) (f : α → γ) (g : β → δ)
    (hfg : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g (φ a) = g (φ b)) :
    (s.image f).card = (t.image g).card := by
  apply Finset.card_bij (fun c hc => g (φ (Finset.mem_image.1 hc).choose))
  · intro c hc
    have h := (Finset.mem_image.1 hc).choose_spec
    exact Finset.mem_image.2 ⟨_, hφ.mapsTo h.1, rfl⟩
  · intro c hc c' hc' heq
    have h := (Finset.mem_image.1 hc).choose_spec
    have h' := (Finset.mem_image.1 hc').choose_spec
    rw [← h.2, ← h'.2]
    exact (hfg _ h.1 _ h'.1).2 heq
  · intro d hd
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨a, ha, rfl⟩ := hφ.surjOn hb
    refine ⟨f a, Finset.mem_image.2 ⟨a, ha, rfl⟩, ?_⟩
    have h := (Finset.mem_image.1 (Finset.mem_image.2 ⟨a, ha, rfl⟩ : f a ∈ s.image f)).choose_spec
    exact (hfg _ h.1 _ ha).1 h.2

lemma lineCount_comp (z : (∀ i, T (e i)) → F) (i : ι) :
    lineCount (e i) (fun ω' => z (Φ e ω')) = lineCount i z := by
  unfold lineCount
  symm
  apply card_image_eq _ _ (fun ω => (Φ e).symm ω)
  · refine ⟨?_, ?_, ?_⟩
    · intro ω hω
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
      simpa using hω
    · intro ω _ ω' _ h; exact (Φ e).symm.injective h
    · intro ω' hω'
      refine ⟨Φ e ω', ?_, by simp⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω' ⊢
      exact hω'
  · intro a _ b _
    constructor
    · intro h
      funext j
      obtain ⟨j0, hj0⟩ := j
      obtain ⟨j', rfl⟩ := e.surjective j0
      have hj' : j' ≠ i := fun h' => hj0 (by rw [h'])
      have := congrFun h ⟨j', hj'⟩
      simp only at this
      have ha : ((Φ e).symm a) (e j') = a j' := by
        exact Φsymm_e e a j'
      have hb : ((Φ e).symm b) (e j') = b j' := by
        exact Φsymm_e e b j'
      show ((Φ e).symm a) (e j') = ((Φ e).symm b) (e j')
      rw [ha, hb]; exact this
    · intro h
      funext j
      have hj : e j.1 ≠ e i := fun h' => j.2 (e.injective h')
      have := congrFun h ⟨e j.1, hj⟩
      simp only at this
      have ha : ((Φ e).symm a) (e j.1) = a j.1 := by
        exact Φsymm_e e a j.1
      have hb : ((Φ e).symm b) (e j.1) = b j.1 := by
        exact Φsymm_e e b j.1
      rw [ha, hb] at this; exact this

lemma supportCard_comp (z : (∀ i, T (e i)) → F) :
    supportCard (fun ω' => z (Φ e ω')) = supportCard z := by
  unfold supportCard
  refine Finset.card_nbij' (Φ e) (Φ e).symm ?_ ?_ ?_ ?_
  · intro ω hω; simpa using hω
  · intro ω hω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    simpa using hω
  · intro ω _; simp
  · intro ω _; simp

theorem pe_reindex (C : ∀ k, Submodule F (T k → F)) (ρ : ℝ)
    (h : IsProductExpanding ρ (fun i => C (e i))) : IsProductExpanding ρ C := by
  refine ⟨h.1, fun x' hx' => ?_⟩
  set x : (∀ i, T (e i)) → F := fun ω => x' ((Φ e).symm ω) with hxdef
  have hx : x ∈ ⨆ i, axisCode (fun i => C (e i)) i := by
    refine Submodule.iSup_induction _ (motive := fun x' => (fun ω => x' ((Φ e).symm ω)) ∈
      ⨆ i, axisCode (fun i => C (e i)) i) hx' ?_ ?_ ?_
    · intro k y hy
      obtain ⟨i, rfl⟩ := e.surjective k
      apply Submodule.mem_iSup_of_mem i
      rw [mem_axisCode_iff] at hy ⊢
      intro b
      have := hy ((Φ e).symm b)
      convert this using 2 with s
      rw [Φsymm_update]
    · exact Submodule.zero_mem _
    · intro a b ha hb; exact Submodule.add_mem _ ha hb
  obtain ⟨y, hy, hxy, hbound⟩ := h.2 x hx
  refine ⟨fun k => fun ω' => y (e.symm k) (Φ e ω'), ?_, ?_, ?_⟩
  · intro k
    obtain ⟨i, rfl⟩ := e.surjective k
    simp only [Equiv.symm_apply_apply]
    have := hy i
    rw [mem_axisCode_iff] at this ⊢
    intro b
    have h2 := this (Φ e b)
    convert h2 using 2 with s
    rw [Φ_update]
  · funext ω'
    have := congrFun hxy (Φ e ω')
    simp only [hxdef, Equiv.symm_apply_apply, Finset.sum_apply] at this ⊢
    rw [this]
    exact Fintype.sum_equiv e _ _ (fun c => by simp)
  · have hs : ∑ k, (Fintype.card (T k) : ℝ) *
        (lineCount k (fun ω' => y (e.symm k) (Φ e ω')) : ℝ) =
        ∑ i, (Fintype.card (T (e i)) : ℝ) * (lineCount i (y i) : ℝ) := by
      rw [← Fintype.sum_equiv e (fun i => (Fintype.card (T (e i)) : ℝ) *
        (lineCount (e i) (fun ω' => y (e.symm (e i)) (Φ e ω')) : ℝ)) _ (fun i => rfl)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Equiv.symm_apply_apply]
      rw [lineCount_comp]
    rw [hs]
    have hw : supportCard x' = supportCard x := by
      rw [← supportCard_comp e x]
      congr 1; funext ω'; simp [hxdef]
    rw [hw]; exact hbound

end PrivPCP.PERe


namespace PrivPCP.C43

open GoodQLTC Classical PrivPCP.TDual PrivPCP.RSD Polynomial

variable {q : ℕ} [Fact q.Prime]

lemma subgroupSet_card (S : Subgroup (ZMod q)ˣ) : (subgroupSet S).card = Nat.card S := by
  unfold subgroupSet
  rw [Nat.card_eq_fintype_card]
  have : (Finset.univ.filter fun x : ZMod q => ∃ u ∈ S, (u : ZMod q) = x) =
      (Finset.univ.filter fun u : (ZMod q)ˣ => u ∈ S).image Units.val := by
    ext x; simp
  rw [this, Finset.card_image_of_injective _ Units.val_injective]
  rw [Fintype.card_subtype]

lemma subgroupSet_mul (S : Subgroup (ZMod q)ˣ) :
    ∀ x ∈ subgroupSet S, ∀ y ∈ subgroupSet S, x * y ∈ subgroupSet S := by
  intro x hx y hy
  simp only [subgroupSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u * v, S.mul_mem hu hv, by simp⟩

lemma subgroupSet_zero (S : Subgroup (ZMod q)ˣ) : (0 : ZMod q) ∉ subgroupSet S := by
  simp only [subgroupSet, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
  intro u _ h
  exact u.ne_zero h

variable (Ω H : Finset (ZMod q))

lemma vanishCode_le' (a : ℕ) :
    vanishCode Ω H a ≤ rsCode ((Ω : Finset (ZMod q)) : Set (ZMod q)) (a + 1) :=
  Submodule.map_mono inf_le_left

/-- `U = V^⊥` as a scaled Reed–Solomon code -/
lemma U_eq (hmul : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y ∈ Ω) (h0 : (0 : ZMod q) ∉ Ω) (a : ℕ)
    (ha : a + 1 ≤ Ω.card) :
    dualCode (rsCode (Ω : Set (ZMod q)) (a + 1)) =
      monomialImage (Equiv.refl _) (ux Ω h0) (rsCode (Ω : Set (ZMod q)) (Ω.card - (a + 1))) :=
  dual_rs Ω hmul h0 (a + 1) ha

/-- `W = K^⊥` as a scaled Reed–Solomon code -/
lemma W_eq (hmul : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y ∈ Ω) (h0 : (0 : ZMod q) ∉ Ω) (a : ℕ)
    (hHa : H.card ≤ a) (hdisj : Disjoint H Ω) (ha : a + 1 ≤ Ω.card) :
    dualCode (vanishCode Ω H a) =
      monomialImage (Equiv.refl _) ((Zu Ω H hdisj)⁻¹ * ux Ω h0)
        (rsCode (Ω : Set (ZMod q)) (Ω.card - (a - H.card + 1))) := by
  rw [vanish_eq Ω H a hHa hdisj, dual_monomialImage, dual_rs Ω hmul h0 _ (by omega),
    monomialImage_comp]

lemma finrank_K (a : ℕ) (hHa : H.card ≤ a) (hdisj : Disjoint H Ω) (ha : a + 1 ≤ Ω.card) :
    Module.finrank (ZMod q) (vanishCode Ω H a) = a - H.card + 1 := by
  rw [vanish_eq Ω H a hHa hdisj, finrank_monomialImage, finrank_rsCode Ω _ (by omega)]

end PrivPCP.C43


namespace PrivPCP.C44

lemma rateU (n a h : ℕ) (η : ℝ) (hη : 0 < η) (h1 : η * n ≤ (a : ℝ) - h) (h2 : a + 1 < n) :
    1 ≤ n - (a + 1) ∧ ((n - (a + 1) : ℕ) : ℝ) ≤ (1 - η) * n := by
  refine ⟨by omega, ?_⟩
  rw [Nat.cast_sub (by omega)]
  push_cast
  have : (0 : ℝ) ≤ h := by positivity
  nlinarith

lemma rateW (n a h : ℕ) (η : ℝ) (hη : 0 < η) (h1 : η * n ≤ (a : ℝ) - h) (h2 : a + 1 < n)
    (hha : h ≤ a) :
    1 ≤ n - (a - h + 1) ∧ ((n - (a - h + 1) : ℕ) : ℝ) ≤ (1 - η) * n := by
  refine ⟨by omega, ?_⟩
  rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub hha]
  push_cast
  nlinarith

end PrivPCP.C44

open PrivPCP PrivPCP.C43 PrivPCP.C44 PrivPCP.RSD PrivPCP.PERe PrivPCP.TDual GoodQLTC Classical

theorem solution : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (q : ℕ) [Fact q.Prime] (k : ℕ), 2 ≤ k → ∀ η β ρ : ℝ, 0 < η → η < 1 → 1 ≤ β → 0 < ρ → ρ ≤ 1 →
    (∀ r, 2 ≤ r → r ≤ k → PunctRSPE r η β ρ) →
    ∀ S : Fin k → Subgroup (ZMod q)ˣ,
    (∀ i j, i ≠ j → Nat.Coprime (Nat.card (S i)) (Nat.card (S j))) →
    (∀ i j, β⁻¹ ≤ (Nat.card (S i) : ℝ) / Nat.card (S j) ∧ (Nat.card (S i) : ℝ) / Nat.card (S j) ≤ β) →
    ∀ H : Fin k → Finset (ZMod q), (∀ i, 1 ≤ (H i).card ∧ Disjoint (H i) (subgroupSet (S i))) →
    ∀ a : Fin k → ℕ, (∀ i, η * Nat.card (S i) ≤ (a i : ℝ) - (H i).card ∧ a i + 1 < Nat.card (S i)) →
    ∀ M : (∀ i, ↥((subgroupSet (S i) : Finset (ZMod q)) : Set (ZMod q))) → ZMod q,
      (distTo M (rsNested (fun i => subgroupSet (S i)) H a).Dbig : ℝ) ≤
        Real.exp (C₀ * (k ^ 3 + k ^ 2 * Real.log (1 / ρ))) *
          ∑ i, (distTo M ((rsNested (fun i => subgroupSet (S i)) H a).D i) : ℝ) := by
  obtain ⟨C₀, hC₀, hcor⟩ := PrivPCP.corollary_4_10
  refine ⟨C₀, hC₀, ?_⟩
  intro q _ k hk η β ρ hη0 hη1 hβ hρ0 hρ1 hconj S hcop hbal H hH a ha M
  set Ω : Fin k → Finset (ZMod q) := fun i => subgroupSet (S i) with hΩ
  set X := rsNested Ω H a with hX
  have hn : ∀ i, (Ω i).card = Nat.card (S i) := fun i => subgroupSet_card (S i)
  have hmul : ∀ i, ∀ x ∈ Ω i, ∀ y ∈ Ω i, x * y ∈ Ω i := fun i => subgroupSet_mul (S i)
  have h0 : ∀ i, (0 : ZMod q) ∉ Ω i := fun i => subgroupSet_zero (S i)
  have hHa : ∀ i, (H i).card ≤ a i := by
    intro i
    have h1 := (ha i).1
    have : (0:ℝ) ≤ η * Nat.card (S i) := by positivity
    have : ((H i).card : ℝ) ≤ a i := by linarith
    exact_mod_cast this
  have ha1 : ∀ i, a i + 1 < (Ω i).card := fun i => by rw [hn]; exact (ha i).2
  have hK : ∀ i, Module.finrank (ZMod q) (X.K i) = a i - (H i).card + 1 := fun i =>
    finrank_K (Ω i) (H i) (a i) (hHa i) (hH i).2 (by have := ha1 i; omega)
  have hV : ∀ i, Module.finrank (ZMod q) (X.V i) = a i + 1 := fun i =>
    finrank_rsCode (Ω i) (a i + 1) (by have := ha1 i; omega)
  have hle : ∀ i, X.K i ≤ X.V i := fun i => vanishCode_le' (Ω i) (H i) (a i)
  have hValid : X.Valid := by
    intro i
    refine ⟨?_, lt_of_le_of_ne (hle i) ?_⟩
    · intro h
      have h' : Module.finrank (ZMod q) (X.K i) = 0 := by rw [h]; simp
      have h2 := hK i
      rw [h'] at h2; omega
    · intro h
      have h' : Module.finrank (ZMod q) (X.K i) = Module.finrank (ZMod q) (X.V i) := by rw [h]
      rw [hK, hV] at h'
      have := (hH i).1; have := hHa i; omega
  have hPE : ∀ I : Finset (Fin k), 2 ≤ I.card → ∀ bv : Fin k → Bool,
      IsProductExpanding ρ ((X.restrict I).mixed fun i => bv i.val) := by
    intro I hI2 bv
    have hrk : I.card ≤ k := by
      calc I.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ I
        _ = k := by simp
    let e : Fin I.card ≃ {i // i ∈ I} := I.equivFin.symm
    apply pe_reindex e
    let S' : Fin I.card → Subgroup (ZMod q)ˣ := fun b => S (e b).val
    let tt : Fin I.card → ℕ := fun b => if bv (e b).val then
      (Ω (e b).val).card - (a (e b).val + 1)
      else (Ω (e b).val).card - (a (e b).val - (H (e b).val).card + 1)
    let Λ : ∀ b, ↥((subgroupSet (S' b) : Finset (ZMod q)) : Set (ZMod q)) → (ZMod q)ˣ :=
      fun b => if bv (e b).val then ux (Ω (e b).val) (h0 _)
        else (Zu (Ω (e b).val) (H (e b).val) (hH _).2)⁻¹ * ux (Ω (e b).val) (h0 _)
    have hcodes : (fun b => (X.restrict I).mixed (fun i => bv i.val) (e b)) =
        fun b => monomialImage (Equiv.refl _) (Λ b)
          (rsCode ((subgroupSet (S' b) : Finset (ZMod q)) : Set (ZMod q)) (tt b)) := by
      funext b
      by_cases hb : bv (e b).val = true
      · have hm : (X.restrict I).mixed (fun i => bv i.val) (e b) = dualCode (X.V (e b).val) := by
          simp [NestedCodes.mixed, hb, NestedCodes.U, NestedCodes.restrict]
        rw [hm, show tt b = _ from if_pos hb, show Λ b = _ from if_pos hb]
        exact U_eq (Ω (e b).val) (hmul _) (h0 _) (a (e b).val) (by have := ha1 (e b).val; omega)
      · have hm : (X.restrict I).mixed (fun i => bv i.val) (e b) = dualCode (X.K (e b).val) := by
          simp [NestedCodes.mixed, hb, NestedCodes.W, NestedCodes.restrict]
        rw [hm, show tt b = _ from if_neg hb, show Λ b = _ from if_neg hb]
        exact W_eq (Ω (e b).val) (H (e b).val) (hmul _) (h0 _) (a (e b).val) (hHa _) (hH _).2
          (by have := ha1 (e b).val; omega)
    rw [hcodes]
    refine hconj I.card hI2 hrk q S' ?_ ?_ tt ?_ Λ
    · intro b b' hbb
      apply hcop
      intro h
      exact hbb (e.injective (Subtype.ext h))
    · intro b b'; exact hbal _ _
    · intro b
      by_cases hb : bv (e b).val = true
      · simp only [tt, hb, if_true, S']
        rw [← hn]
        exact rateU _ _ _ η hη0 (by rw [hn]; exact (ha _).1) (ha1 _)
      · simp only [tt, hb, if_false, S']
        rw [← hn]
        exact rateW _ _ _ η hη0 (by rw [hn]; exact (ha _).1) (ha1 _) (hHa _)
  exact hcor (ZMod q) k hk _ X hValid ρ hρ0 hρ1 hPE M


