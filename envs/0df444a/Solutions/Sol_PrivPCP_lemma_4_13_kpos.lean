-- Prove2me | solution 1 for PrivPCP.lemma_4_13_kpos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:49:28.082806+00:00
-- url     : https://prove2.me/submissions/17614771-dc56-4c0b-977e-5f8b00afd0f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PrivPCP_NestedCodes
import Definitions.Def_PrivPCP_rsNested
import Definitions.Def_PrivPCP_gridQ
import Definitions.Def_PrivPCP_certLaw
import Theorems.Thm_PrivPCP_lemma_4_13_mixed
import Definitions.Def_PrivPCP_subgroupSet


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


namespace PrivPCP.R413

open Classical MvPolynomial PrivPCP.L62Aux PrivPCP.Fact33Aux PrivPCP.R411

variable {F : Type} [Field F] [Fintype F]

lemma mem_support_deg {D : MvPolynomial (Fin 2) F} {m : Fin 2 →₀ ℕ} (hm : m ∈ D.support) (i : Fin 2) :
    m i ≤ D.degreeOf i := le_degreeOf_of_mem hm i

/-- evaluation of a polynomial not involving `X₁` only depends on the image of `X₀` -/
lemma aeval_pure0 (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 1 = 0) {A : Type} [CommRing A]
    [Algebra F A] (f g : Fin 2 → A) (h0 : f 0 = g 0) : aeval f D = aeval g D := by
  conv_lhs => rw [D.as_sum]
  conv_rhs => rw [D.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  congr 1
  refine Finsupp.prod_congr fun i hi => ?_
  have : i = 0 := by
    fin_cases i
    · rfl
    · exfalso; rw [Finsupp.mem_support_iff] at hi
      have := mem_support_deg hm 1; exact hi (Nat.le_zero.1 (hD ▸ this))
  subst this; rw [h0]

lemma aeval_pure1 (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 0 = 0) {A : Type} [CommRing A]
    [Algebra F A] (f g : Fin 2 → A) (h1 : f 1 = g 1) : aeval f D = aeval g D := by
  conv_lhs => rw [D.as_sum]
  conv_rhs => rw [D.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  congr 1
  refine Finsupp.prod_congr fun i hi => ?_
  have : i = 1 := by
    fin_cases i
    · exfalso; rw [Finsupp.mem_support_iff] at hi
      have := mem_support_deg hm 0; exact hi (Nat.le_zero.1 (hD ▸ this))
    · rfl
  subst this; rw [h1]

lemma aeval_X0_colP (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 1 = 0) (β : F) :
    Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F) (colP β D) = D := by
  unfold colP
  rw [← AlgHom.comp_apply, comp_aeval]
  conv_rhs => rw [← aeval_X_left_apply D]
  exact aeval_pure0 D hD _ _ (by simp)

lemma aeval_X1_rowP (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 0 = 0) (α : F) :
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) F) (rowP α D) = D := by
  unfold rowP
  rw [← AlgHom.comp_apply, comp_aeval]
  conv_rhs => rw [← aeval_X_left_apply D]
  exact aeval_pure1 D hD _ _ (by simp)

/-- Lagrange basis on a finset of field elements -/
noncomputable def lbas (B : Finset F) (β : F) : Polynomial F := Lagrange.basis B id β

lemma eval_lbas (B : Finset F) (β b : F) (hβ : β ∈ B) (hb : b ∈ B) :
    (lbas B β).eval b = if β = b then 1 else 0 := by
  unfold lbas
  split_ifs with h
  · subst h
    have := Lagrange.eval_basis_self (v := (id : F → F)) (Set.injOn_id _) hβ
    simpa using this
  · have := Lagrange.eval_basis_of_ne (v := (id : F → F)) (s := B) h hb
    simpa using this

lemma natDegree_lbas (B : Finset F) (β : F) (hβ : β ∈ B) : (lbas B β).natDegree < B.card := by
  unfold lbas
  rw [Lagrange.natDegree_basis (Set.injOn_id _) hβ]
  have : 0 < B.card := Finset.card_pos.mpr ⟨β, hβ⟩
  omega

lemma eval_fin2 (z : Fin 2 → F) (P : MvPolynomial (Fin 2) F) : eval z P = eval ![z 0, z 1] P := by
  rw [fin2_eq]

/-- interpolation in the `Y` direction -/
noncomputable def interpY (B : Finset F) (G : MvPolynomial (Fin 2) F) : MvPolynomial (Fin 2) F :=
  ∑ β ∈ B, Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F) (colP β G) *
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) F) (lbas B β)

noncomputable def interpX (A : Finset F) (G : MvPolynomial (Fin 2) F) : MvPolynomial (Fin 2) F :=
  ∑ α ∈ A, Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F) (lbas A α) *
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) F) (rowP α G)

lemma interpY_eq (A B : Finset F) (G : MvPolynomial (Fin 2) F) (hGA : G.degreeOf 0 < A.card)
    (hGB : G.degreeOf 1 < B.card) : interpY B G = G := by
  apply eq_of_evGrid_eq ![A, B]
  · intro l; fin_cases l
    · show _ < A.card
      refine lt_of_le_of_lt ((degreeOf_sum_le _ _ _).trans (Finset.sup_le fun β _ => ?_)) hGA
      refine (degreeOf_mul_le _ _ _).trans ?_
      have h1 := degreeOf_aeval_X_le (0 : Fin 2) (0 : Fin 2) (colP β G)
      have h2 := degreeOf_aeval_X_le (1 : Fin 2) (0 : Fin 2) (lbas B β)
      rw [if_pos rfl] at h1
      rw [if_neg (show (0 : Fin 2) ≠ 1 by decide)] at h2
      have := natDegree_colP β G
      exact (add_le_add h1 h2).trans (by omega)
    · show _ < B.card
      have hB : 0 < B.card := by omega
      refine lt_of_le_of_lt ((degreeOf_sum_le _ _ _).trans (Finset.sup_le fun β hβ => ?_))
        (show B.card - 1 < B.card by omega)
      refine (degreeOf_mul_le _ _ _).trans ?_
      have h1 := degreeOf_aeval_X_le (0 : Fin 2) (1 : Fin 2) (colP β G)
      have h2 := degreeOf_aeval_X_le (1 : Fin 2) (1 : Fin 2) (lbas B β)
      rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h1
      rw [if_pos rfl] at h2
      have := natDegree_lbas B β hβ
      exact (add_le_add h1 h2).trans (by omega)
  · intro l; fin_cases l
    · exact hGA
    · exact hGB
  · funext x
    rw [evGrid_eq, evGrid_eq]
    unfold interpY
    rw [map_sum]
    have hx1 : (x 1 : F) ∈ B := by simpa using (x 1).2
    rw [Finset.sum_eq_single (x 1 : F)]
    · rw [map_mul, eval_aeval_X, eval_aeval_X]
      simp only [gpt]
      rw [eval_lbas B _ _ hx1 hx1, if_pos rfl, mul_one, eval_colP]
      rw [gpt2]
    · intro β hβ hne
      rw [map_mul, eval_aeval_X, eval_aeval_X]
      simp only [gpt]
      rw [eval_lbas B _ _ hβ hx1, if_neg hne, mul_zero]
    · intro h; exact absurd hx1 h

lemma interpX_eq (A B : Finset F) (G : MvPolynomial (Fin 2) F) (hGA : G.degreeOf 0 < A.card)
    (hGB : G.degreeOf 1 < B.card) : interpX A G = G := by
  apply eq_of_evGrid_eq ![A, B]
  · intro l; fin_cases l
    · show _ < A.card
      have hA : 0 < A.card := by omega
      refine lt_of_le_of_lt ((degreeOf_sum_le _ _ _).trans (Finset.sup_le fun α hα => ?_))
        (show A.card - 1 < A.card by omega)
      refine (degreeOf_mul_le _ _ _).trans ?_
      have h1 := degreeOf_aeval_X_le (0 : Fin 2) (0 : Fin 2) (lbas A α)
      have h2 := degreeOf_aeval_X_le (1 : Fin 2) (0 : Fin 2) (rowP α G)
      rw [if_pos rfl] at h1
      rw [if_neg (show (0 : Fin 2) ≠ 1 by decide)] at h2
      have := natDegree_lbas A α hα
      exact (add_le_add h1 h2).trans (by omega)
    · show _ < B.card
      refine lt_of_le_of_lt ((degreeOf_sum_le _ _ _).trans (Finset.sup_le fun α _ => ?_)) hGB
      refine (degreeOf_mul_le _ _ _).trans ?_
      have h1 := degreeOf_aeval_X_le (0 : Fin 2) (1 : Fin 2) (lbas A α)
      have h2 := degreeOf_aeval_X_le (1 : Fin 2) (1 : Fin 2) (rowP α G)
      rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h1
      rw [if_pos rfl] at h2
      have := natDegree_rowP α G
      exact (add_le_add h1 h2).trans (by omega)
  · intro l; fin_cases l
    · exact hGA
    · exact hGB
  · funext x
    rw [evGrid_eq, evGrid_eq]
    unfold interpX
    rw [map_sum]
    have hx0 : (x 0 : F) ∈ A := by simpa using (x 0).2
    rw [Finset.sum_eq_single (x 0 : F)]
    · rw [map_mul, eval_aeval_X, eval_aeval_X]
      simp only [gpt]
      rw [eval_lbas A _ _ hx0 hx0, if_pos rfl, one_mul, eval_rowP]
      rw [gpt2]
    · intro α hα hne
      rw [map_mul, eval_aeval_X, eval_aeval_X]
      simp only [gpt]
      rw [eval_lbas A _ _ hα hx0, if_neg hne, zero_mul]
    · intro h; exact absurd hx0 h

/-- a polynomial in `X` dividing many columns divides the whole polynomial -/
lemma int_div_col (G D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 1 = 0) (A B : Finset F)
    (hGA : G.degreeOf 0 < A.card) (hGB : G.degreeOf 1 < B.card)
    (h : ∀ β ∈ B, colP β D ∣ colP β G) : D ∣ G := by
  rw [← interpY_eq A B G hGA hGB]
  unfold interpY
  refine Finset.dvd_sum fun β hβ => ?_
  obtain ⟨R, hR⟩ := h β hβ
  rw [hR, map_mul, aeval_X0_colP D hD, mul_assoc]
  exact dvd_mul_right _ _

lemma int_div_row (G V : MvPolynomial (Fin 2) F) (hV : V.degreeOf 0 = 0) (A B : Finset F)
    (hGA : G.degreeOf 0 < A.card) (hGB : G.degreeOf 1 < B.card)
    (h : ∀ α ∈ A, rowP α V ∣ rowP α G) : V ∣ G := by
  rw [← interpX_eq A B G hGA hGB]
  unfold interpX
  refine Finset.dvd_sum fun α hα => ?_
  obtain ⟨R, hR⟩ := h α hα
  rw [hR, map_mul, aeval_X1_rowP V hV, ← mul_assoc, mul_comm _ V, mul_assoc]
  exact dvd_mul_right _ _

end PrivPCP.R413


namespace PrivPCP.R413

open Classical MvPolynomial PrivPCP.L62Aux PrivPCP.Fact33Aux PrivPCP.R411

variable {F : Type} [Field F] [Fintype F]

lemma degreeOf_unit {u : MvPolynomial (Fin 2) F} (hu : IsUnit u) (i : Fin 2) : u.degreeOf i = 0 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have := degreeOf_mul_eq (n := i) hu0 hv0
  rw [hv, ← C_1, degreeOf_C] at this
  omega

lemma not_isUnit_lin (α : F) (i : Fin 2) : ¬ IsUnit (X i - C α : MvPolynomial (Fin 2) F) := by
  intro h
  have h2 := h.map (eval (fun _ => α))
  simp at h2

lemma rowP_ne_zero_of_irred (G : MvPolynomial (Fin 2) F) (hG : Irreducible G) (h1 : 0 < G.degreeOf 1)
    (A B : Finset F) (hA : G.degreeOf 0 < A.card) (hB : G.degreeOf 1 < B.card) (α : F) :
    rowP α G ≠ 0 := by
  intro h0
  set D : MvPolynomial (Fin 2) F := X 0 - C α
  have hD1 : D.degreeOf 1 = 0 := by
    have : D.degreeOf 1 ≤ max ((X 0 : MvPolynomial (Fin 2) F).degreeOf 1) ((C α : MvPolynomial (Fin 2) F).degreeOf 1) :=
      degreeOf_sub_le _ _ _
    rw [degreeOf_X, degreeOf_C, if_neg (by decide)] at this
    omega
  have hDG : D ∣ G := by
    apply int_div_col G D hD1 A B hA hB
    intro β _
    have : colP β D = Polynomial.X - Polynomial.C α := by simp [D, colP]
    rw [this, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_colP, ← eval_rowP, h0,
      Polynomial.eval_zero]
  obtain ⟨u, hu⟩ := hDG
  rcases hG.isUnit_or_isUnit hu with hD | hu'
  · exact not_isUnit_lin α 0 hD
  · have hD0 : D ≠ 0 := by rintro hD; rw [hD, zero_mul] at hu; exact hG.ne_zero hu
    have := degreeOf_mul_eq (n := (1 : Fin 2)) hD0 hu'.ne_zero
    rw [← hu, hD1, degreeOf_unit hu'] at this
    omega

lemma colP_ne_zero_of_irred (G : MvPolynomial (Fin 2) F) (hG : Irreducible G) (h0 : 0 < G.degreeOf 0)
    (A B : Finset F) (hA : G.degreeOf 0 < A.card) (hB : G.degreeOf 1 < B.card) (β : F) :
    colP β G ≠ 0 := by
  intro hc
  set D : MvPolynomial (Fin 2) F := X 1 - C β
  have hD0' : D.degreeOf 0 = 0 := by
    have : D.degreeOf 0 ≤ max ((X 1 : MvPolynomial (Fin 2) F).degreeOf 0) ((C β : MvPolynomial (Fin 2) F).degreeOf 0) :=
      degreeOf_sub_le _ _ _
    rw [degreeOf_X, degreeOf_C, if_neg (by decide)] at this
    omega
  have hDG : D ∣ G := by
    apply int_div_row G D hD0' A B hA hB
    intro α _
    have : rowP α D = Polynomial.X - Polynomial.C β := by simp [D, rowP]
    rw [this, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_rowP, ← eval_colP, hc,
      Polynomial.eval_zero]
  obtain ⟨u, hu⟩ := hDG
  rcases hG.isUnit_or_isUnit hu with hD | hu'
  · exact not_isUnit_lin β 1 hD
  · have hD0 : D ≠ 0 := by rintro hD; rw [hD, zero_mul] at hu; exact hG.ne_zero hu
    have := degreeOf_mul_eq (n := (0 : Fin 2)) hD0 hu'.ne_zero
    rw [← hu, hD0', degreeOf_unit hu'] at this
    omega

/-- a polynomial without mixed irreducible factors splits as `U(X) V(Y)` -/
lemma pure_split (E : MvPolynomial (Fin 2) F) (hE : E ≠ 0)
    (h : ∀ G, Irreducible G → G ∣ E → G.degreeOf 0 = 0 ∨ G.degreeOf 1 = 0) :
    ∃ U V : MvPolynomial (Fin 2) F, E = U * V ∧ U.degreeOf 1 = 0 ∧ V.degreeOf 0 = 0 := by
  induction E using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hE
  | h₂ x hx => exact ⟨x, 1, (mul_one x).symm, degreeOf_unit hx 1, by rw [← C_1, degreeOf_C]⟩
  | h₃ a p ha hp ih =>
    obtain ⟨U, V, rfl, hU, hV⟩ := ih ha (fun G hG hGa => h G hG (dvd_mul_of_dvd_right hGa p))
    have hp0 : p ≠ 0 := hp.ne_zero
    rcases h p hp.irreducible (dvd_mul_right p _) with h0 | h1
    · refine ⟨U, p * V, by ring, hU, ?_⟩
      have := degreeOf_mul_le (0 : Fin 2) p V
      omega
    · refine ⟨p * U, V, by ring, ?_, hV⟩
      have := degreeOf_mul_le (1 : Fin 2) p U
      omega

def Rows (A : Finset F) (E P : MvPolynomial (Fin 2) F) : Prop :=
  ∀ α ∈ A, ∃ R : Polynomial F, rowP α P = rowP α E * R
def Cols (B : Finset F) (E P : MvPolynomial (Fin 2) F) : Prop :=
  ∀ β ∈ B, ∃ R : Polynomial F, colP β P = colP β E * R

theorem div_main (A B : Finset F) (k1 k2 : ℕ) (hk1 : 1 ≤ k1) (hk2 : 1 ≤ k2) (τ : ℝ)
    (hτ : ∀ e : ℕ, (e : ℝ) ≤ τ → k1 + e ≤ A.card ∧ k2 + e ≤ B.card)
    (Hmix : ∀ E P : MvPolynomial (Fin 2) F, E ≠ 0 → (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ →
      P.degreeOf 0 < k1 + E.degreeOf 0 → P.degreeOf 1 < k2 + E.degreeOf 1 → Rows A E P →
      Cols B E P → ∀ G, Irreducible G → G ∣ E → 0 < G.degreeOf 0 → 0 < G.degreeOf 1 → G ∣ P) :
    ∀ n, ∀ E P : MvPolynomial (Fin 2) F, E.degreeOf 0 + E.degreeOf 1 = n → E ≠ 0 →
      (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ →
      P.degreeOf 0 < k1 + E.degreeOf 0 → P.degreeOf 1 < k2 + E.degreeOf 1 → Rows A E P →
      Cols B E P → E ∣ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E P hn hE hτE hPX hPY hR hC
  have hA0 := (hτ _ (le_trans (le_max_left _ _) hτE)).1
  have hB1 := (hτ _ (le_trans (le_max_right _ _) hτE)).2
  by_cases hP : P = 0
  · rw [hP]; exact dvd_zero E
  by_cases hmix : ∃ G, Irreducible G ∧ G ∣ E ∧ 0 < G.degreeOf 0 ∧ 0 < G.degreeOf 1
  · obtain ⟨G, hG, hGE, hG0, hG1⟩ := hmix
    have hGP := Hmix E P hE hτE hPX hPY hR hC G hG hGE hG0 hG1
    obtain ⟨E', rfl⟩ := hGE
    obtain ⟨P', rfl⟩ := hGP
    have hGn : G ≠ 0 := hG.ne_zero
    have hE' : E' ≠ 0 := right_ne_zero_of_mul hE
    have hP' : P' ≠ 0 := right_ne_zero_of_mul hP
    have dE0 := degreeOf_mul_eq (n := (0 : Fin 2)) hGn hE'
    have dE1 := degreeOf_mul_eq (n := (1 : Fin 2)) hGn hE'
    have dP0 := degreeOf_mul_eq (n := (0 : Fin 2)) hGn hP'
    have dP1 := degreeOf_mul_eq (n := (1 : Fin 2)) hGn hP'
    have hrowG : ∀ α, rowP α G ≠ 0 := rowP_ne_zero_of_irred G hG hG1 A B (by omega) (by omega)
    have hcolG : ∀ β, colP β G ≠ 0 := colP_ne_zero_of_irred G hG hG0 A B (by omega) (by omega)
    have hR' : Rows A E' P' := by
      intro α hα
      obtain ⟨R, hR⟩ := hR α hα
      refine ⟨R, ?_⟩
      rw [rowP_mul, rowP_mul, mul_assoc] at hR
      exact mul_left_cancel₀ (hrowG α) hR
    have hC' : Cols B E' P' := by
      intro β hβ
      obtain ⟨R, hR⟩ := hC β hβ
      refine ⟨R, ?_⟩
      rw [colP_mul, colP_mul, mul_assoc] at hR
      exact mul_left_cancel₀ (hcolG β) hR
    have hτ' : (max (E'.degreeOf 0) (E'.degreeOf 1) : ℝ) ≤ τ := by
      refine le_trans ?_ hτE
      rw [dE0, dE1]
      push_cast
      exact max_le_max (by linarith) (by linarith)
    have := ih (E'.degreeOf 0 + E'.degreeOf 1) (by omega) E' P' rfl hE' hτ' (by omega) (by omega)
      hR' hC'
    exact mul_dvd_mul_left G this
  · push Not at hmix
    obtain ⟨U, V, rfl, hU, hV⟩ := pure_split E hE (fun G hG hGE => by
      by_cases h0 : G.degreeOf 0 = 0
      · exact Or.inl h0
      · right; have := hmix G hG hGE (by omega); omega)
    have hU0 : U ≠ 0 := left_ne_zero_of_mul hE
    have hV0 : V ≠ 0 := right_ne_zero_of_mul hE
    have d0 := degreeOf_mul_eq (n := (0 : Fin 2)) hU0 hV0
    have d1 := degreeOf_mul_eq (n := (1 : Fin 2)) hU0 hV0
    have hVP : V ∣ P := by
      apply int_div_row P V hV A B (by omega) (by omega)
      intro α hα
      obtain ⟨R, hR⟩ := hR α hα
      rw [rowP_mul] at hR
      exact ⟨rowP α U * R, by rw [hR]; ring⟩
    obtain ⟨P1, rfl⟩ := hVP
    have hP1 : P1 ≠ 0 := right_ne_zero_of_mul hP
    have e0 := degreeOf_mul_eq (n := (0 : Fin 2)) hV0 hP1
    have e1 := degreeOf_mul_eq (n := (1 : Fin 2)) hV0 hP1
    set v := rowP 0 V with hvdef
    have hv : v ≠ 0 := by
      intro h0; apply hV0; rw [← aeval_X1_rowP V hV 0, ← hvdef, h0, map_zero]
    set Bg := B.filter fun β => v.eval β ≠ 0 with hBg
    have hcard : B.card ≤ Bg.card + v.natDegree := card_nonzero_ge v hv B
    have hvd : v.natDegree ≤ V.degreeOf 1 := natDegree_rowP 0 V
    have hcolV : ∀ β ∈ Bg, colP β V ≠ 0 := by
      intro β hβ h0
      have := (Finset.mem_filter.1 hβ).2
      apply this
      rw [hvdef, eval_rowP, ← eval_colP, h0, Polynomial.eval_zero]
    have hUP : U ∣ P1 := by
      apply int_div_col P1 U hU A Bg (by omega) (by omega)
      intro β hβ
      obtain ⟨C, hC'⟩ := hC β (Finset.mem_filter.1 hβ).1
      rw [colP_mul, colP_mul] at hC'
      exact ⟨C, mul_left_cancel₀ (hcolV β hβ) (by rw [hC']; ring)⟩
    obtain ⟨Q, rfl⟩ := hUP
    exact ⟨Q, by ring⟩

end PrivPCP.R413


namespace PrivPCP.R413

open Classical MvPolynomial

lemma card_subgroupSet' {q : ℕ} [Fact q.Prime] (S : Subgroup (ZMod q)ˣ) :
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

lemma mem_subgroupSet' {q : ℕ} [Fact q.Prime] (S : Subgroup (ZMod q)ˣ) (u : (ZMod q)ˣ) (hu : u ∈ S) :
    (u : ZMod q) ∈ subgroupSet S :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, u, hu, rfl⟩

lemma tau_bound (c1 h n1 n2 : ℝ) (hc1 : 0 < c1) (hc1' : c1 ≤ 1 / 2) (hh : 0 ≤ h) (hn1 : 0 < n1)
    (hn2 : 0 < n2) (hh1 : h ≤ n1) (hh2 : h ≤ n2) : c1 * h ^ 3 / (n1 * n2) ≤ h := by
  have hN : 0 < n1 * n2 := mul_pos hn1 hn2
  rw [div_le_iff₀ hN]
  have hhN : h * h ≤ n1 * n2 := mul_le_mul hh1 hh2 hh hn1.le
  have e1 : h ^ 3 = h * (h * h) := by ring
  rw [e1]
  have a := mul_le_mul_of_nonneg_left hhN hh
  have b : c1 * (h * (h * h)) ≤ 1 * (h * (h * h)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

end PrivPCP.R413

open PrivPCP PrivPCP.R413 PrivPCP.R411 Classical MvPolynomial in
theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
      Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
      ∀ k₁ k₂ : ℕ, 1 ≤ k₁ → 1 ≤ k₂ → k₁ < Nat.card S₁ → k₂ < Nat.card S₂ →
      ∀ E P : MvPolynomial (Fin 2) (ZMod q), E ≠ 0 →
        (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤
          c₀ * ((min (Nat.card S₁ - k₁) (Nat.card S₂ - k₂) : ℕ) : ℝ) ^ 3 / ((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) →
        P.degreeOf 0 < k₁ + E.degreeOf 0 →
        P.degreeOf 1 < k₂ + E.degreeOf 1 →
        (∀ α ∈ S₁, ∃ R : Polynomial (ZMod q),
          MvPolynomial.aeval (![Polynomial.C (α : ZMod q), Polynomial.X] : Fin 2 → Polynomial (ZMod q)) P =
            MvPolynomial.aeval (![Polynomial.C (α : ZMod q), Polynomial.X] : Fin 2 → Polynomial (ZMod q)) E * R) →
        (∀ β ∈ S₂, ∃ Cβ : Polynomial (ZMod q),
          MvPolynomial.aeval (![Polynomial.X, Polynomial.C (β : ZMod q)] : Fin 2 → Polynomial (ZMod q)) P =
            MvPolynomial.aeval (![Polynomial.X, Polynomial.C (β : ZMod q)] : Fin 2 → Polynomial (ZMod q)) E * Cβ) →
        E ∣ P ∧ ∃ Q : MvPolynomial (Fin 2) (ZMod q), P = E * Q ∧ Q.degreeOf 0 < k₁ ∧ Q.degreeOf 1 < k₂ := by
  obtain ⟨c0, hc0, Hm⟩ := PrivPCP.lemma_4_13_mixed
  refine ⟨min c0 (1 / 2), lt_min hc0 (by norm_num), ?_⟩
  intro q _ S₁ S₂ hcop k₁ k₂ hk1 hk2 hk1n hk2n E P hE hmax hPX hPY hrow hcol
  have hc1 : 0 < min c0 (1 / 2) := lt_min hc0 (by norm_num)
  have hc1' : min c0 (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hc10 : min c0 (1 / 2) ≤ c0 := min_le_left _ _
  set A := subgroupSet S₁ with hAdef
  set B := subgroupSet S₂ with hBdef
  have hA : A.card = Nat.card S₁ := card_subgroupSet' S₁
  have hB : B.card = Nat.card S₂ := card_subgroupSet' S₂
  set n1 := Nat.card S₁ with hn1
  set n2 := Nat.card S₂ with hn2
  set h := min (n1 - k₁) (n2 - k₂) with hhdef
  set τ : ℝ := min c0 (1 / 2) * (h : ℝ) ^ 3 / ((n1 * n2 : ℕ) : ℝ) with hτdef
  have hhn1 : h ≤ n1 := (Nat.min_le_left _ _).trans (Nat.sub_le _ _)
  have hhn2 : h ≤ n2 := (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have hh1 : h ≤ n1 - k₁ := Nat.min_le_left _ _
  have hh2 : h ≤ n2 - k₂ := Nat.min_le_right _ _
  have hτh : τ ≤ h := by
    rw [hτdef]; push_cast
    exact tau_bound _ _ _ _ hc1 hc1' (by positivity) (by exact_mod_cast (show 0 < n1 by omega))
      (by exact_mod_cast (show 0 < n2 by omega)) (by exact_mod_cast hhn1) (by exact_mod_cast hhn2)
  have hτ : ∀ e : ℕ, (e : ℝ) ≤ τ → k₁ + e ≤ A.card ∧ k₂ + e ≤ B.card := by
    intro e he
    have : e ≤ h := by exact_mod_cast he.trans hτh
    rw [hA, hB]; omega
  have hτc0 : τ ≤ c0 * (h : ℝ) ^ 3 / ((n1 * n2 : ℕ) : ℝ) := by
    rw [hτdef]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hc10 (by positivity)
  have Hmix : ∀ E P : MvPolynomial (Fin 2) (ZMod q), E ≠ 0 →
      (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ →
      P.degreeOf 0 < k₁ + E.degreeOf 0 → P.degreeOf 1 < k₂ + E.degreeOf 1 → Rows A E P →
      Cols B E P → ∀ G, Irreducible G → G ∣ E → 0 < G.degreeOf 0 → 0 < G.degreeOf 1 → G ∣ P := by
    intro E P hE hm hPX hPY hR hC
    exact Hm q S₁ S₂ hcop k₁ k₂ hk1n hk2n E P hE (hm.trans hτc0) hPX hPY
      (fun α hα => hR (α : ZMod q) (mem_subgroupSet' S₁ α hα))
      (fun β hβ => hC (β : ZMod q) (mem_subgroupSet' S₂ β hβ))
  have hR : Rows A E P := by
    intro a ha
    obtain ⟨-, u, hu, rfl⟩ := Finset.mem_filter.1 ha
    exact hrow u hu
  have hC : Cols B E P := by
    intro b hb
    obtain ⟨-, u, hu, rfl⟩ := Finset.mem_filter.1 hb
    exact hcol u hu
  have hdiv := div_main A B k₁ k₂ hk1 hk2 τ hτ Hmix _ E P rfl hE hmax hPX hPY hR hC
  refine ⟨hdiv, ?_⟩
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨Q, hQ, ?_⟩
  by_cases hQ0 : Q = 0
  · rw [hQ0, degreeOf_zero, degreeOf_zero]; exact ⟨hk1, hk2⟩
  · have d0 := degreeOf_mul_eq (n := (0 : Fin 2)) hE hQ0
    have d1 := degreeOf_mul_eq (n := (1 : Fin 2)) hE hQ0
    rw [← hQ] at d0 d1
    constructor <;> omega


