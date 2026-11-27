-- Prove2me | solution 1 for PrivPCP.corollary_4_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:10:11.631439+00:00
-- url     : https://prove2.me/submissions/31dac4fd-3cc3-4a32-877a-8db8d6aad8c5

import Mathlib
import Definitions.Def_PrivPCP_NestedCodes
import Definitions.Def_PrivPCP_IsCollectivelyPE


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


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

abbrev Om (S : ι → Type) (I : Finset ι) : Type := ∀ i : {i // i ∈ I}, S i.val

/-- glue a value at `t` with a word on `I \ {t}` -/
def ext {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t)) : Om S I :=
  fun i => if h : i.val = t then cast (congrArg S h.symm) x
    else y ⟨i.val, Finset.mem_erase.2 ⟨h, i.2⟩⟩

def res {I : Finset ι} {t : ι} (ht : t ∈ I) (ω : Om S I) : Om S (I.erase t) :=
  fun j => ω ⟨j.val, Finset.mem_of_mem_erase j.2⟩

abbrev tpt {I : Finset ι} {t : ι} (ht : t ∈ I) : {i // i ∈ I} := ⟨t, ht⟩

lemma ext_at {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t)) :
    ext ht x y (tpt ht) = x := by
  unfold ext tpt
  rw [dif_pos rfl]
  rfl

lemma ext_ne {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t))
    (i : {i // i ∈ I}) (h : i.val ≠ t) :
    ext ht x y i = y ⟨i.val, Finset.mem_erase.2 ⟨h, i.2⟩⟩ := by
  unfold ext
  rw [dif_neg h]

lemma res_ext {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t)) :
    res ht (ext ht x y) = y := by
  funext j
  simp only [res]
  rw [ext_ne ht x y _ (Finset.ne_of_mem_erase j.2)]

lemma ext_res {I : Finset ι} {t : ι} (ht : t ∈ I) (ω : Om S I) :
    ext ht (ω (tpt ht)) (res ht ω) = ω := by
  funext i
  by_cases h : i.val = t
  · have hi : i = tpt ht := Subtype.ext h
    subst hi
    exact ext_at ht _ _
  · unfold ext; rw [dif_neg h]; rfl

lemma ext_eq_update {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (b : Om S I) :
    ext ht x (res ht b) = Function.update b (tpt ht) x := by
  funext i
  by_cases h : i.val = t
  · have hi : i = tpt ht := Subtype.ext h
    subst hi
    exact (ext_at ht _ _).trans (Function.update_self (tpt ht) x b).symm
  · have hne : i ≠ tpt ht := fun h' => h (congrArg Subtype.val h')
    rw [Function.update_of_ne hne]
    unfold ext; rw [dif_neg h]; rfl

lemma update_ext_ne {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t))
    (j : {i // i ∈ I.erase t}) (s : S j.val) :
    Function.update (ext ht x y) ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s =
      ext ht x (Function.update y j s) := by
  funext i
  by_cases h : i.val = t
  · have hi : i = tpt ht := Subtype.ext h
    subst hi
    have hne : (tpt ht : {i // i ∈ I}) ≠ ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := by
      intro h'; exact Finset.ne_of_mem_erase j.2 (congrArg Subtype.val h').symm
    rw [Function.update_of_ne hne, ext_at, ext_at]
  · rw [ext_ne ht _ _ i h]
    by_cases hij : i.val = j.val
    · have hi : i = ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := Subtype.ext hij
      subst hi
      rw [Function.update_self]
      have : (⟨j.val, Finset.mem_erase.2 ⟨h, Finset.mem_of_mem_erase j.2⟩⟩ :
        {i // i ∈ I.erase t}) = j := Subtype.ext rfl
      exact (Function.update_self j s y).symm
    · have hne : i ≠ ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := fun h' => hij (congrArg Subtype.val h')
      have hne' : (⟨i.val, Finset.mem_erase.2 ⟨h, i.2⟩⟩ : {i // i ∈ I.erase t}) ≠ j :=
        fun h' => hij (congrArg Subtype.val h')
      rw [Function.update_of_ne hne, ext_ne ht _ _ i h, Function.update_of_ne hne']

/-- the gluing equivalence -/
def extEquiv {I : Finset ι} {t : ι} (ht : t ∈ I) : S t × Om S (I.erase t) ≃ Om S I where
  toFun p := ext ht p.1 p.2
  invFun ω := (ω (tpt ht), res ht ω)
  left_inv p := by simp [ext_at, res_ext]
  right_inv ω := ext_res ht ω

lemma sum_ext {I : Finset ι} {t : ι} (ht : t ∈ I) (f : Om S I → F) :
    ∑ ω, f ω = ∑ x, ∑ y, f (ext ht x y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (extEquiv ht) _ _ (fun _ => rfl)).symm

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

/-- contraction along coordinate `t` -/
def contr {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) (Z : Om S I → F) :
    Om S (I.erase t) → F :=
  fun y => ∑ x, v x * Z (ext ht x y)

/-- tensor lift `u ⊗ P` -/
def tl {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F) :
    Om S I → F :=
  fun ω => u (ω (tpt ht)) * P (res ht ω)

lemma res_update_t {I : Finset ι} {t : ι} (ht : t ∈ I) (b : Om S I) (s : S t) :
    res ht (Function.update b (tpt ht) s) = res ht b := by
  rw [← ext_eq_update, res_ext]

lemma update_t_at {I : Finset ι} {t : ι} (ht : t ∈ I) (b : Om S I) (s : S t) :
    (Function.update b (tpt ht) s) (tpt ht) = s := Function.update_self _ _ _

lemma res_update_ne {I : Finset ι} {t : ι} (ht : t ∈ I) (b : Om S I)
    (j : {i // i ∈ I.erase t}) (s : S j.val) :
    res ht (Function.update b ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s) =
      Function.update (res ht b) j s := by
  conv_lhs => rw [← ext_res ht b]
  rw [update_ext_ne, res_ext]

lemma update_ne_at {I : Finset ι} {t : ι} (ht : t ∈ I) (b : Om S I)
    (j : {i // i ∈ I.erase t}) (s : S j.val) :
    (Function.update b ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s) (tpt ht) = b (tpt ht) := by
  apply Function.update_of_ne
  intro h
  exact Finset.ne_of_mem_erase j.2 (congrArg Subtype.val h).symm

lemma line_dot_contr {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) (Z : Om S I → F)
    (b : Om S I) :
    v ⬝ᵥ (fun s => Z (Function.update b (tpt ht) s)) = contr ht v Z (res ht b) := by
  simp only [dotProduct, contr]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ext_eq_update]

lemma contr_sum {I : Finset ι} {t : ι} (ht : t ∈ I) {m : ℕ} (c : Fin m → F) (bv : Fin m → S t → F)
    (Z : Om S I → F) :
    contr ht (∑ n, c n • bv n) Z = ∑ n, c n • contr ht (bv n) Z := by
  funext y
  simp only [contr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun x _ => by ring

lemma contr_sub {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) (Z Z' : Om S I → F) :
    contr ht v (Z - Z') = contr ht v Z - contr ht v Z' := by
  funext y; simp [contr, mul_sub, Finset.sum_sub_distrib]

lemma contr_fsum {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) {m : ℕ}
    (Z : Fin m → Om S I → F) :
    contr ht v (∑ n, Z n) = ∑ n, contr ht v (Z n) := by
  funext y; simp only [contr, Finset.sum_apply, Finset.mul_sum]; rw [Finset.sum_comm]

lemma contr_tl {I : Finset ι} {t : ι} (ht : t ∈ I) (v u : S t → F) (P : Om S (I.erase t) → F) :
    contr ht v (tl ht u P) = (v ⬝ᵥ u) • P := by
  funext y
  simp only [contr, tl, ext_at, res_ext, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => by ring

lemma dot_tl {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F)
    (Z : Om S I → F) : tl ht u P ⬝ᵥ Z = P ⬝ᵥ contr ht u Z := by
  rw [dotProduct, sum_ext ht]
  simp only [tl, ext_at, res_ext, dotProduct, contr, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- lines of a tensor lift in a direction other than `t` -/
lemma tl_line_ne {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F)
    (j : {i // i ∈ I.erase t}) (Cj : Submodule F (S j.val → F))
    (hP : ∀ b', (fun s => P (Function.update b' j s)) ∈ Cj) (b : Om S I) :
    (fun s => tl ht u P (Function.update b ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s)) ∈ Cj := by
  have : (fun s => tl ht u P (Function.update b ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s)) =
      u (b (tpt ht)) • (fun s => P (Function.update (res ht b) j s)) := by
    funext s
    simp only [tl, Pi.smul_apply, smul_eq_mul]
    rw [update_ne_at, res_update_ne]
  rw [this]
  exact Cj.smul_mem _ (hP _)

/-- lines of a tensor lift in direction `t` -/
lemma tl_line_t {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F)
    (Ct : Submodule F (S t → F)) (hu : u ∈ Ct) (b : Om S I) :
    (fun s => tl ht u P (Function.update b (tpt ht) s)) ∈ Ct := by
  have : (fun s => tl ht u P (Function.update b (tpt ht) s)) = P (res ht b) • u := by
    funext s
    simp only [tl, Pi.smul_apply, smul_eq_mul]
    rw [update_t_at, res_update_t, mul_comm]
  rw [this]
  exact Ct.smul_mem _ hu

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]

section generic
variable {κ : Type} [Fintype κ] [DecidableEq κ] {T : κ → Type} [∀ i, Fintype (T i)]

lemma axisCode_congr (C C' : ∀ i, Submodule F (T i → F)) (j : κ) (h : C j = C' j) :
    axisCode C j = axisCode C' j := by
  ext x; rw [mem_axisCode_iff, mem_axisCode_iff, h]

lemma axisCode_mono (C C' : ∀ i, Submodule F (T i → F)) (j : κ) (h : C j ≤ C' j) :
    axisCode C j ≤ axisCode C' j := by
  intro x hx; rw [mem_axisCode_iff] at hx ⊢; exact fun b => h (hx b)

lemma tensorCode_mono (C C' : ∀ i, Submodule F (T i → F)) (h : ∀ j, C j ≤ C' j) :
    tensorCode C ≤ tensorCode C' := iInf_mono fun j => axisCode_mono C C' j (h j)

variable (Y : NestedCodes F κ T)

lemma Kbig_le_C (hKV : ∀ i, Y.K i ≤ Y.V i) : Y.Kbig ≤ Y.C := by
  apply iSup_le
  intro i
  apply tensorCode_mono
  intro j
  by_cases h : j = i
  · subst h; rw [Function.update_self]; exact hKV j
  · rw [Function.update_of_ne h]

lemma B_le_Dbig (hKV : ∀ i, Y.K i ≤ Y.V i) : Y.B ≤ Y.Dbig :=
  dualCode_antitone (Kbig_le_C Y hKV)

lemma B_eq : Y.B = ⨆ j, axisCode Y.U j := dualCode_tensorCode Y.V

lemma Dbig_le_dualE (i : κ) : Y.Dbig ≤ dualCode (Y.E i) :=
  dualCode_antitone (le_iSup Y.E i)

lemma dualE_eq (i : κ) :
    dualCode (Y.E i) = ⨆ j, axisCode (fun j => dualCode (Function.update Y.V i (Y.K i) j)) j :=
  dualCode_tensorCode _

end generic

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

lemma functional_eq_dot' {Ω : Type} [Fintype Ω] (ℓ : (Ω → F) →ₗ[F] F) (v : Ω → F) :
    ℓ v = (fun x => ℓ (Pi.single x 1)) ⬝ᵥ v := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  congr 2
  funext y
  simp [Pi.single_apply, eq_comm]

lemma tl_zero {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) :
    tl ht u (0 : Om S (I.erase t) → F) = 0 := by funext ω; simp [tl]

lemma tl_add {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P P' : Om S (I.erase t) → F) :
    tl ht u (P + P') = tl ht u P + tl ht u P' := by funext ω; simp [tl, mul_add]

variable (X : NestedCodes F ι S)

lemma tl_mem_B {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F)
    (hP : P ∈ (X.restrict (I.erase t)).B) : tl ht u P ∈ (X.restrict I).B := by
  rw [B_eq] at hP ⊢
  refine Submodule.iSup_induction _ (motive := fun P => tl ht u P ∈ _) hP ?_ ?_ ?_
  · intro j P hPj
    apply Submodule.mem_iSup_of_mem (⟨j.val, Finset.mem_of_mem_erase j.2⟩ : {i // i ∈ I})
    rw [mem_axisCode_iff]
    intro b
    exact tl_line_ne ht u P j _ ((mem_axisCode_iff _ _ _).1 hPj) b
  · rw [tl_zero]; exact Submodule.zero_mem _
  · intro P P' h1 h2; rw [tl_add]; exact Submodule.add_mem _ h1 h2

lemma code_eq {I : Finset ι} {t : ι} (j m : {i // i ∈ I.erase t}) :
    (Function.update (X.restrict I).V ⟨j.val, Finset.mem_of_mem_erase j.2⟩
        ((X.restrict I).K ⟨j.val, Finset.mem_of_mem_erase j.2⟩))
      ⟨m.val, Finset.mem_of_mem_erase m.2⟩ =
    (Function.update (X.restrict (I.erase t)).V j ((X.restrict (I.erase t)).K j)) m := by
  by_cases h : m = j
  · subst h; simp [Function.update_self]; rfl
  · have h' : (⟨m.val, Finset.mem_of_mem_erase m.2⟩ : {i // i ∈ I}) ≠
        ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := by
      intro e; apply h; apply Subtype.ext; have := congrArg Subtype.val e; simpa using this
    rw [Function.update_of_ne h', Function.update_of_ne h]; rfl

lemma tl_mem_Kbig {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) (hv : v ∈ X.V t)
    (R : Om S (I.erase t) → F) (hR : R ∈ (X.restrict (I.erase t)).Kbig) :
    tl ht v R ∈ (X.restrict I).Kbig := by
  refine Submodule.iSup_induction _ (motive := fun P => tl ht v P ∈ _) hR ?_ ?_ ?_
  · intro j P hPj
    apply Submodule.mem_iSup_of_mem (⟨j.val, Finset.mem_of_mem_erase j.2⟩ : {i // i ∈ I})
    unfold NestedCodes.E tensorCode at hPj ⊢
    rw [Submodule.mem_iInf] at hPj ⊢
    intro m
    rw [mem_axisCode_iff]
    intro b
    by_cases hm : m = tpt ht
    · subst hm
      have hne : (tpt ht : {i // i ∈ I}) ≠ ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := by
        intro e; exact Finset.ne_of_mem_erase j.2 (congrArg Subtype.val e).symm
      rw [Function.update_of_ne hne]
      exact tl_line_t ht v P (X.V t) hv b
    · have hmt : m.val ≠ t := fun e => hm (Subtype.ext e)
      let mJ : {i // i ∈ I.erase t} := ⟨m.val, Finset.mem_erase.2 ⟨hmt, m.2⟩⟩
      have hl := (mem_axisCode_iff _ _ _).1 (hPj mJ)
      have := tl_line_ne ht v P mJ _ hl b
      rw [← code_eq X j mJ] at this
      exact this
  · rw [tl_zero]; exact Submodule.zero_mem _
  · intro P P' h1 h2; rw [tl_add]; exact Submodule.add_mem _ h1 h2

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

theorem step (hKV : ∀ i, X.K i ≤ X.V i) (I : Finset ι) (t : ι) (ht : t ∈ I)
    (ρ c : ℝ) (hρ : 0 ≤ ρ)
    (hPE : IsProductExpanding ρ ((X.restrict I).mixed fun i => decide (i.val ≠ t)))
    (IH : ∀ M' ∈ (X.restrict (I.erase t)).Dbig, M' ∉ (X.restrict (I.erase t)).B →
      c ≤ supportCard M') :
    ∀ M ∈ (X.restrict I).Dbig, M ∉ (X.restrict I).B →
      ρ * Fintype.card (S t) * c ≤ supportCard M := by
  intro M hM hMB
  have hKVI : ∀ i, (X.restrict I).K i ≤ (X.restrict I).V i := fun i => hKV i.val
  have hfam : (fun j => dualCode (Function.update (X.restrict I).V (tpt ht)
      ((X.restrict I).K (tpt ht)) j)) = (X.restrict I).mixed (fun i => decide (i.val ≠ t)) := by
    funext j
    by_cases h : j = tpt ht
    · subst h
      simp only [Function.update_self, NestedCodes.mixed, ne_eq, not_true_eq_false,
        decide_false]
      rfl
    · have : j.val ≠ t := fun h' => h (Subtype.ext h')
      rw [Function.update_of_ne h]
      simp only [NestedCodes.mixed, ne_eq, this, not_false_eq_true, decide_true, if_true]
      rfl
  have hMa : M ∈ ⨆ j, axisCode ((X.restrict I).mixed fun i => decide (i.val ≠ t)) j := by
    have := Dbig_le_dualE (X.restrict I) (tpt ht) hM
    rw [dualE_eq, hfam] at this; exact this
  obtain ⟨y, hy, hMy, hbound⟩ := hPE.2 M hMa
  set Mt := y (tpt ht) with hMtdef
  have hyB : ∀ j, j ≠ tpt ht → y j ∈ (X.restrict I).B := by
    intro j hj
    rw [B_eq]
    apply Submodule.mem_iSup_of_mem j
    have hjt : j.val ≠ t := fun h' => hj (Subtype.ext h')
    rw [axisCode_congr (X.restrict I).U ((X.restrict I).mixed fun i => decide (i.val ≠ t)) j
      (by simp [NestedCodes.mixed, hjt])]
    exact hy j
  have hrest : M - Mt ∈ (X.restrict I).B := by
    rw [hMy, ← Finset.add_sum_erase _ _ (Finset.mem_univ (tpt ht)), add_sub_cancel_left]
    exact Submodule.sum_mem _ fun j hj => hyB j (Finset.ne_of_mem_erase hj)
  have hMtD : Mt ∈ (X.restrict I).Dbig := by
    have : Mt = M - (M - Mt) := by abel
    rw [this]; exact Submodule.sub_mem _ hM (B_le_Dbig _ hKVI hrest)
  have hMtB : Mt ∉ (X.restrict I).B := by
    intro h; apply hMB
    have : M = (M - Mt) + Mt := by abel
    rw [this]; exact Submodule.add_mem _ hrest h
  -- a contraction that is not in `B`
  have hex : ∃ v ∈ X.V t, contr ht v Mt ∉ (X.restrict (I.erase t)).B := by
    by_contra hcon
    push Not at hcon
    apply hMtB
    let bV := Module.finBasis F (X.V t)
    have hext : ∀ m, ∃ g : (S t → F) →ₗ[F] F, g.comp (X.V t).subtype = bV.coord m :=
      fun m => LinearMap.exists_extend (bV.coord m)
    choose g hg using hext
    let u : Fin (Module.finrank F (X.V t)) → S t → F := fun m s => g m (Pi.single s 1)
    have hu : ∀ m (w : X.V t), u m ⬝ᵥ (w : S t → F) = bV.coord m w := by
      intro m w
      rw [← hg m]
      exact (functional_eq_dot' (g m) w).symm
    set N := Mt - ∑ m, tl ht (u m) (contr ht (bV m) Mt) with hNdef
    have hN : N ∈ (X.restrict I).B := by
      rw [B_eq]
      apply Submodule.mem_iSup_of_mem (tpt ht)
      rw [mem_axisCode_iff]
      intro b v hv
      rw [line_dot_contr]
      have hv' : v = ∑ m, (bV.coord m ⟨v, hv⟩) • (bV m : S t → F) := by
        have h1 := bV.sum_repr ⟨v, hv⟩
        have h2 := congrArg Subtype.val h1
        rw [Submodule.coe_sum] at h2
        simp only [SetLike.val_smul] at h2
        conv_lhs => rw [← h2]
        rfl
      rw [hNdef, contr_sub, contr_fsum]
      simp only [contr_tl]
      have : contr ht v Mt = ∑ m, (bV.coord m ⟨v, hv⟩) • contr ht (bV m) Mt := by
        conv_lhs => rw [hv']
        exact contr_sum ht _ _ Mt
      rw [this]
      have h2 : ∀ m, (v ⬝ᵥ u m) = bV.coord m ⟨v, hv⟩ := by
        intro m; rw [dotProduct_comm]; exact hu m ⟨v, hv⟩
      simp only [h2, sub_self, Pi.zero_apply]
    have hsum : ∑ m, tl ht (u m) (contr ht (bV m) Mt) ∈ (X.restrict I).B :=
      Submodule.sum_mem _ fun m _ => tl_mem_B X ht (u m) _ (hcon _ (bV m).2)
    have : Mt = N + ∑ m, tl ht (u m) (contr ht (bV m) Mt) := by rw [hNdef]; abel
    rw [this]; exact Submodule.add_mem _ hN hsum
  obtain ⟨v, hv, hvB⟩ := hex
  -- the contraction lies in `D` of the smaller tuple
  have hcD : contr ht v Mt ∈ (X.restrict (I.erase t)).Dbig := by
    intro R hR
    rw [← dot_tl]
    exact hMtD _ (tl_mem_Kbig X ht v hv R hR)
  have hc := IH _ hcD hvB
  -- weight of the contraction
  have hwt : supportCard (contr ht v Mt) ≤ lineCount (tpt ht) Mt := by
    unfold supportCard lineCount
    let f : Om S (I.erase t) → ((j : {j : {i // i ∈ I} // j ≠ tpt ht}) → S j.1.val) :=
      fun y j => y ⟨j.1.val, Finset.mem_erase.2 ⟨fun h => j.2 (Subtype.ext h), j.1.2⟩⟩
    apply Finset.card_le_card_of_injOn f
    · intro y hy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy
      obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      have hx' : Mt (ext ht x y) ≠ 0 := right_ne_zero_of_mul hx
      simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
        Set.mem_setOf_eq]
      refine ⟨ext ht x y, hx', ?_⟩
      funext j
      exact ext_ne ht x y j.1 (fun h => j.2 (Subtype.ext h))
    · intro y _ y' _ hyy
      funext jJ
      have := congrFun hyy ⟨⟨jJ.val, Finset.mem_of_mem_erase jJ.2⟩,
        fun h => Finset.ne_of_mem_erase jJ.2 (congrArg Subtype.val h)⟩
      simpa [f] using this
  have hle : (Fintype.card (S t) : ℝ) * (lineCount (tpt ht) Mt : ℝ) ≤
      ∑ j, (Fintype.card (S j.val) : ℝ) * (lineCount j (y j) : ℝ) :=
    Finset.single_le_sum (f := fun j => (Fintype.card (S j.val) : ℝ) * (lineCount j (y j) : ℝ))
      (fun j _ => by positivity) (Finset.mem_univ (tpt ht))
  have hs : (0 : ℝ) ≤ ρ * Fintype.card (S t) := by positivity
  calc ρ * Fintype.card (S t) * c
      ≤ ρ * Fintype.card (S t) * (supportCard (contr ht v Mt) : ℝ) :=
        mul_le_mul_of_nonneg_left hc hs
    _ ≤ ρ * Fintype.card (S t) * (lineCount (tpt ht) Mt : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hwt) hs
    _ = ρ * ((Fintype.card (S t) : ℝ) * (lineCount (tpt ht) Mt : ℝ)) := by ring
    _ ≤ ρ * ∑ j, (Fintype.card (S j.val) : ℝ) * (lineCount j (y j) : ℝ) :=
        mul_le_mul_of_nonneg_left hle hρ
    _ ≤ supportCard M := hbound

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

theorem base (I : Finset ι) (t : ι) (ht : t ∈ I) (hI : I.erase t = ∅) :
    ∀ M ∈ (X.restrict I).Dbig, M ∉ (X.restrict I).B →
      ((sInf {d | ∃ w ∈ X.W t, w ∉ X.U t ∧ supportCard w = d} : ℕ) : ℝ) ≤ supportCard M := by
  intro M hM hMB
  have hall : ∀ j : {i // i ∈ I}, j = tpt ht := by
    intro j
    apply Subtype.ext
    by_contra h
    have : j.val ∈ I.erase t := Finset.mem_erase.2 ⟨h, j.2⟩
    rw [hI] at this; simp at this
  have hMa := Dbig_le_dualE (X.restrict I) (tpt ht) hM
  rw [dualE_eq] at hMa
  have hle : (⨆ j, axisCode (fun j => dualCode (Function.update (X.restrict I).V (tpt ht)
      ((X.restrict I).K (tpt ht)) j)) j) ≤ axisCode (fun j => dualCode (Function.update
      (X.restrict I).V (tpt ht) ((X.restrict I).K (tpt ht)) j)) (tpt ht) := by
    apply iSup_le; intro j; rw [hall j]
  have hMW := hle hMa
  rw [mem_axisCode_iff] at hMW
  simp only [Function.update_self] at hMW
  have hMU : M ∉ axisCode (X.restrict I).U (tpt ht) := by
    intro h; apply hMB; rw [B_eq]; exact Submodule.mem_iSup_of_mem (tpt ht) h
  rw [mem_axisCode_iff] at hMU
  push Not at hMU
  obtain ⟨b, hb⟩ := hMU
  have h1 : sInf {d | ∃ w ∈ X.W t, w ∉ X.U t ∧ supportCard w = d} ≤
      supportCard (fun s => M (Function.update b (tpt ht) s)) :=
    Nat.sInf_le ⟨_, hMW b, hb, rfl⟩
  have h2 : supportCard (fun s => M (Function.update b (tpt ht) s)) ≤ supportCard M := by
    unfold supportCard
    apply Finset.card_le_card_of_injOn (fun s => Function.update b (tpt ht) s)
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs ⊢
      exact hs
    · intro s _ s' _ h
      have := congrFun h (tpt ht)
      simpa using this
  exact_mod_cast h1.trans h2

/-! transport from `restrict I` with `I` containing everything -/

section transport
variable (I : Finset ι) (hI : ∀ i, i ∈ I)

def Tm (ω : ∀ i, S i) : Om S I := fun i => ω i.val
def Ti (ω : Om S I) : ∀ i, S i := fun i => ω ⟨i, hI i⟩

lemma Tm_Ti (ω : Om S I) : Tm I (Ti I hI ω) = ω := by funext i; rfl
lemma Ti_Tm (ω : ∀ i, S i) : Ti I hI (Tm I ω) = ω := by funext i; rfl

lemma Tm_update (b : ∀ i, S i) (j : ι) (s : S j) :
    Tm I (Function.update b j s) = Function.update (Tm I b) ⟨j, hI j⟩ s := by
  funext i
  by_cases h : i.val = j
  · have hi : i = ⟨j, hI j⟩ := Subtype.ext h
    subst hi
    simp [Tm]
  · have hne : i ≠ ⟨j, hI j⟩ := fun e => h (congrArg Subtype.val e)
    rw [Function.update_of_ne hne]
    simp only [Tm]; rw [Function.update_of_ne h]

lemma Ti_update (b : Om S I) (j : {i // i ∈ I}) (s : S j.val) :
    Ti I hI (Function.update b j s) = Function.update (Ti I hI b) j.val s := by
  funext i
  by_cases h : i = j.val
  · subst h; simp [Ti]
  · have hne : (⟨i, hI i⟩ : {i // i ∈ I}) ≠ j := fun e => h (congrArg Subtype.val e)
    rw [Function.update_of_ne h]
    simp only [Ti]; rw [Function.update_of_ne hne]

def TEquiv : (∀ i, S i) ≃ Om S I where
  toFun := Tm I
  invFun := Ti I hI
  left_inv := Ti_Tm I hI
  right_inv := Tm_Ti I hI

lemma dot_T (x : Om S I → F) (y : (∀ i, S i) → F) :
    (fun ω => x (Tm I ω)) ⬝ᵥ y = x ⬝ᵥ (fun ω => y (Ti I hI ω)) := by
  unfold dotProduct
  exact Fintype.sum_equiv (TEquiv I hI) _ _ (fun ω => by simp [TEquiv, Ti_Tm])

include hI in
lemma axis_pull (C : ∀ i, Submodule F (S i → F)) (j : {i // i ∈ I}) (x : Om S I → F)
    (hx : x ∈ axisCode (fun i : {i // i ∈ I} => C i.val) j) :
    (fun ω => x (Tm I ω)) ∈ axisCode C j.val := by
  rw [mem_axisCode_iff] at hx ⊢
  intro b
  have := hx (Tm I b)
  convert this using 2 with s
  rw [Tm_update I hI]

lemma axis_push (C : ∀ i, Submodule F (S i → F)) (j : ι) (x : (∀ i, S i) → F)
    (hx : x ∈ axisCode C j) :
    (fun ω => x (Ti I hI ω)) ∈ axisCode (fun i : {i // i ∈ I} => C i.val) ⟨j, hI j⟩ := by
  rw [mem_axisCode_iff] at hx ⊢
  intro b
  have := hx (Ti I hI b)
  convert this using 2 with s
  rw [Ti_update I hI]

end transport

end PrivPCP.L46Aux


namespace PrivPCP.Lemma48Aux

open Classical GoodQLTC

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

/-- the `I`-flat through `ω`: points agreeing with `ω` outside `I` -/
noncomputable def flat (I : Finset ι) (ω : ∀ i, S i) : Finset (∀ i, S i) :=
  Finset.univ.filter fun ω' => ∀ j, j ∉ I → ω' j = ω j

lemma mem_flat {I : Finset ι} {ω ω' : ∀ i, S i} : ω' ∈ flat I ω ↔ ∀ j, j ∉ I → ω' j = ω j := by
  simp [flat]

lemma self_mem_flat (I : Finset ι) (ω : ∀ i, S i) : ω ∈ flat I ω := mem_flat.2 fun _ _ => rfl

lemma flat_eq_of_mem {I : Finset ι} {ω ω' : ∀ i, S i} (h : ω' ∈ flat I ω) :
    flat I ω' = flat I ω := by
  rw [mem_flat] at h
  ext x
  simp only [mem_flat]
  constructor
  · intro hx j hj; rw [hx j hj, h j hj]
  · intro hx j hj; rw [hx j hj, h j hj]

lemma flat_mono {I J : Finset ι} (h : I ⊆ J) (ω : ∀ i, S i) : flat I ω ⊆ flat J ω := by
  intro x hx
  rw [mem_flat] at hx ⊢
  exact fun j hj => hx j (fun hI => hj (h hI))

lemma flat_eq_piFinset (I : Finset ι) (ω : ∀ i, S i) :
    flat I ω = Fintype.piFinset (fun i => if i ∈ I then Finset.univ else {ω i}) := by
  ext x
  simp only [mem_flat, Fintype.mem_piFinset]
  constructor
  · intro h i
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi, h i hi]
  · intro h j hj
    have := h j
    simpa [hj] using this

lemma card_flat (I : Finset ι) (ω : ∀ i, S i) :
    (flat I ω).card = ∏ i ∈ I, Fintype.card (S i) := by
  rw [flat_eq_piFinset, Fintype.card_piFinset]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ I)]
  have h1 : ∏ x ∈ Finset.univ.filter (fun i => i ∈ I),
      (if x ∈ I then (Finset.univ : Finset (S x)) else {ω x}).card =
      ∏ i ∈ I, Fintype.card (S i) := by
    rw [Finset.filter_univ_mem]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [hi]
  have h2 : ∏ x ∈ Finset.univ.filter (fun i => ¬ i ∈ I),
      (if x ∈ I then (Finset.univ : Finset (S x)) else {ω x}).card = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp only [Finset.mem_filter] at hi
    simp [hi.2]
  rw [h1, h2, mul_one]

lemma update_mem_flat (ω : ∀ i, S i) (i : ι) (t : S i) :
    Function.update ω i t ∈ flat {i} ω := by
  rw [mem_flat]
  intro j hj
  rw [Finset.mem_singleton] at hj
  rw [Function.update_of_ne hj]

/-- projection forgetting coordinate `i` (the line index used by `lineCount`) -/
def proj (i : ι) (ω : ∀ i, S i) : (j : {j // j ≠ i}) → S j.1 := fun j => ω j.1

lemma proj_eq_iff (i : ι) (ω ω' : ∀ i, S i) : proj i ω' = proj i ω ↔ ω' ∈ flat {i} ω := by
  rw [mem_flat]
  constructor
  · intro h j hj
    rw [Finset.mem_singleton] at hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j.1 (by simpa using j.2)

/-- the fiber of the line index `β` -/
noncomputable def fiber (i : ι) (β : (j : {j // j ≠ i}) → S j.1) : Finset (∀ i, S i) :=
  Finset.univ.filter fun ω => proj i ω = β

lemma fiber_proj (i : ι) (ω : ∀ i, S i) : fiber i (proj i ω) = flat {i} ω := by
  ext x
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
  exact proj_eq_iff i ω x

end PrivPCP.Lemma48Aux


namespace PrivPCP.Lemma48Aux

open Classical GoodQLTC

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

/-- `ρ`-closed sets -/
def IsClosedSet (ρ : ℝ) (B : Finset (∀ i, S i)) : Prop :=
  ∀ i ω, ¬ flat {i} ω ⊆ B → ((B ∩ flat {i} ω).card : ℝ) < ρ * Fintype.card (S i)

/-- heavy flats -/
def heavy (ε : ℝ) (A : Finset (∀ i, S i)) (I : Finset ι) (ω : ∀ i, S i) : Prop :=
  (∏ i ∈ I, ε * (Fintype.card (S i) : ℝ)) ≤ ((A ∩ flat I ω).card : ℝ)

lemma heavy_congr {ε : ℝ} {A : Finset (∀ i, S i)} {I : Finset ι} {ω ω' : ∀ i, S i}
    (h : ω' ∈ flat I ω) : heavy ε A I ω' ↔ heavy ε A I ω := by
  rw [heavy, heavy, flat_eq_of_mem h]

noncomputable def closureSet (ε : ℝ) (A : Finset (∀ i, S i)) : Finset (∀ i, S i) :=
  Finset.univ.filter fun ω => ∃ I, heavy ε A I ω

lemma subset_closureSet (ε : ℝ) (A : Finset (∀ i, S i)) : A ⊆ closureSet ε A := by
  intro ω hω
  simp only [closureSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨∅, ?_⟩
  simp only [heavy, Finset.prod_empty, Nat.one_le_cast]
  exact Finset.card_pos.mpr ⟨ω, Finset.mem_inter.mpr ⟨hω, self_mem_flat _ _⟩⟩

lemma card_inter_flat_sum (A : Finset (∀ i, S i)) (I : Finset ι) :
    ∑ ω, (A ∩ flat I ω).card = A.card * ∏ i ∈ I, Fintype.card (S i) := by
  have hsymm : ∀ a ω : ∀ i, S i, a ∈ flat I ω ↔ ω ∈ flat I a := by
    intro a ω; simp only [mem_flat]
    exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
  have : ∀ ω, (A ∩ flat I ω).card = ∑ a ∈ A, if ω ∈ flat I a then 1 else 0 := by
    intro ω
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hsymm]
  simp_rw [this]
  rw [Finset.sum_comm]
  have h2 : ∀ a, (∑ ω : (∀ i, S i), if ω ∈ flat I a then 1 else 0) = (flat I a).card := by
    intro a
    rw [← Finset.card_filter]
    congr 1
    ext x; simp
  simp_rw [h2, card_flat, Finset.sum_const, smul_eq_mul]

lemma closureSet_closed {ρ : ℝ} (hρ : 0 < ρ) (A : Finset (∀ i, S i)) :
    IsClosedSet ρ (closureSet (ρ / 2 ^ Fintype.card ι) A) := by
  set ε := ρ / 2 ^ Fintype.card ι with hε
  have hεpos : 0 < ε := by positivity
  intro i ω hnot
  have hspos : (0 : ℝ) < Fintype.card (S i) := by
    have : Nonempty (S i) := ⟨ω i⟩
    exact_mod_cast Fintype.card_pos
  set B := closureSet ε A
  -- each term
  have hterm : ∀ I : Finset ι,
      (((Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω).card : ℝ) <
        ε * Fintype.card (S i) := by
    intro I
    set T := (Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω with hT
    by_cases hiI : i ∈ I
    · have hT0 : T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [hT, Finset.mem_inter, Finset.mem_filter] at hx
        obtain ⟨⟨-, hhx⟩, hxf⟩ := hx
        apply hnot
        intro y hy
        have hxI : x ∈ flat I ω := flat_mono (by simpa using hiI) ω hxf
        have hyI : y ∈ flat I ω := flat_mono (by simpa using hiI) ω hy
        have : heavy ε A I y := by
          rw [heavy_congr hyI]; rw [heavy_congr hxI] at hhx; exact hhx
        simp only [B, closureSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨I, this⟩
      rw [hT0, Finset.card_empty, Nat.cast_zero]
      positivity
    · by_contra hge
      push Not at hge
      apply hnot
      set J := insert i I
      have hheavy : heavy ε A J ω := by
        unfold heavy
        rw [Finset.prod_insert hiI]
        have hprod_nonneg : 0 ≤ ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ) :=
          Finset.prod_nonneg fun _ _ => by positivity
        calc ε * (Fintype.card (S i) : ℝ) * ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ)
            ≤ (T.card : ℝ) * ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ) :=
              mul_le_mul_of_nonneg_right hge hprod_nonneg
          _ ≤ ∑ x ∈ T, ((A ∩ flat I x).card : ℝ) := by
              rw [← nsmul_eq_mul]
              rw [← Finset.sum_const]
              refine Finset.sum_le_sum fun x hx => ?_
              rw [hT, Finset.mem_inter, Finset.mem_filter] at hx
              exact hx.1.2
          _ = ((T.biUnion fun x => A ∩ flat I x).card : ℝ) := by
              rw [Finset.card_biUnion]
              · push_cast; rfl
              · intro x hx x' hx' hne
                rw [Function.onFun, Finset.disjoint_left]
                intro y hy hy'
                apply hne
                rw [Finset.mem_coe, hT, Finset.mem_inter] at hx hx'
                have h1 := mem_flat.1 (Finset.mem_inter.1 hy).2 i hiI
                have h2 := mem_flat.1 (Finset.mem_inter.1 hy').2 i hiI
                funext j
                by_cases hj : j = i
                · subst hj; rw [← h1, ← h2]
                · have := mem_flat.1 hx.2 j (by simpa using hj)
                  have h' := mem_flat.1 hx'.2 j (by simpa using hj)
                  rw [this, h']
          _ ≤ ((A ∩ flat J ω).card : ℝ) := by
              norm_cast
              apply Finset.card_le_card
              intro y hy
              rw [Finset.mem_biUnion] at hy
              obtain ⟨x, hx, hy⟩ := hy
              rw [hT, Finset.mem_inter] at hx
              rw [Finset.mem_inter] at hy ⊢
              refine ⟨hy.1, ?_⟩
              rw [mem_flat]
              intro j hj
              have hji : j ≠ i := fun h => hj (by simp [J, h])
              have hjI : j ∉ I := fun h => hj (by simp [J, h])
              rw [mem_flat.1 hy.2 j hjI, mem_flat.1 hx.2 j (by simpa using hji)]
      intro y hy
      have hyJ : y ∈ flat J ω := flat_mono (by simp [J]) ω hy
      simp only [B, closureSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨J, (heavy_congr hyJ).2 hheavy⟩
  -- sum up
  have hBsub : B ∩ flat {i} ω ⊆
      (Finset.univ : Finset (Finset ι)).biUnion
        fun I => (Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω := by
    intro x hx
    rw [Finset.mem_inter] at hx
    simp only [B, closureSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨I, hI⟩, hxf⟩ := hx
    rw [Finset.mem_biUnion]
    exact ⟨I, Finset.mem_univ _, Finset.mem_inter.2 ⟨by simpa using hI, hxf⟩⟩
  calc ((B ∩ flat {i} ω).card : ℝ)
      ≤ (((Finset.univ : Finset (Finset ι)).biUnion
        fun I => (Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hBsub
    _ ≤ ∑ I : Finset ι, (((Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ < ∑ _I : Finset ι, ε * (Fintype.card (S i) : ℝ) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun I _ => hterm I
    _ = ρ * Fintype.card (S i) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, hε]
        push_cast
        field_simp

lemma closureSet_card {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (A : Finset (∀ i, S i)) :
    ((closureSet (ρ / 2 ^ Fintype.card ι) A).card : ℝ) ≤
      ((2 ^ Fintype.card ι + 1) / ρ) ^ Fintype.card ι * A.card := by
  set ε := ρ / 2 ^ Fintype.card ι with hε
  have hεpos : 0 < ε := by positivity
  by_cases hne : (closureSet ε A).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp; positivity
  obtain ⟨ω₀, -⟩ := hne
  have hspos : ∀ i, (0 : ℝ) < Fintype.card (S i) := by
    intro i
    have : Nonempty (S i) := ⟨ω₀ i⟩
    exact_mod_cast Fintype.card_pos
  have hI : ∀ I : Finset ι, (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) ≤
      A.card * (1 / ε) ^ I.card := by
    intro I
    have hP : 0 < ∏ i ∈ I, (Fintype.card (S i) : ℝ) := Finset.prod_pos fun i _ => hspos i
    have key : (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) *
        (ε ^ I.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ)) ≤
        A.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ) := by
      have hprod : (ε ^ I.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ)) =
          ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      rw [hprod]
      calc (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) *
            ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ)
          ≤ ∑ x ∈ Finset.univ.filter (fun x => heavy ε A I x), ((A ∩ flat I x).card : ℝ) := by
            rw [← nsmul_eq_mul, ← Finset.sum_const]
            refine Finset.sum_le_sum fun x hx => ?_
            exact (Finset.mem_filter.1 hx).2
        _ ≤ ∑ x, ((A ∩ flat I x).card : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
        _ = A.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ) := by
            have := card_inter_flat_sum A I
            exact_mod_cast this
    have hpos : 0 < ε ^ I.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ) := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have key' : (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) * ε ^ I.card *
        ∏ i ∈ I, (Fintype.card (S i) : ℝ) ≤ A.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ) := by
      rw [mul_assoc]; exact key
    exact le_of_mul_le_mul_right key' hP
  have hsub : closureSet ε A ⊆ (Finset.univ : Finset (Finset ι)).biUnion
      fun I => Finset.univ.filter fun x => heavy ε A I x := by
    intro x hx
    simp only [closureSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨I, hI⟩ := hx
    rw [Finset.mem_biUnion]
    exact ⟨I, Finset.mem_univ _, by simpa using hI⟩
  calc ((closureSet ε A).card : ℝ)
      ≤ (((Finset.univ : Finset (Finset ι)).biUnion
          fun I => Finset.univ.filter fun x => heavy ε A I x).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ I : Finset ι, (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ I : Finset ι, A.card * (1 / ε) ^ I.card := Finset.sum_le_sum fun I _ => hI I
    _ = A.card * (1 / ε + 1) ^ Fintype.card ι := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.sum_pow_mul_eq_add_pow (1 / ε) (1 : ℝ) (Finset.univ : Finset ι)
        rw [Finset.powerset_univ, Finset.card_univ] at this
        simpa using this
    _ ≤ ((2 ^ Fintype.card ι + 1) / ρ) ^ Fintype.card ι * A.card := by
        rw [mul_comm]
        gcongr
        rw [hε, one_div_div, div_add_one hρ.ne', ]
        gcongr

end PrivPCP.Lemma48Aux


namespace PrivPCP.Lemma48Aux

open Classical GoodQLTC

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

lemma biUnion_flat_eq (i : ι) (P : Finset (∀ i, S i)) :
    P.biUnion (fun ω => flat {i} ω) = (P.image (proj i)).biUnion (fiber i) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨ω, hω, hx⟩
    exact ⟨proj i ω, ⟨ω, hω, rfl⟩, by rw [fiber_proj]; exact hx⟩
  · rintro ⟨β, ⟨ω, hω, rfl⟩, hx⟩
    exact ⟨ω, hω, by rw [← fiber_proj]; exact hx⟩

lemma card_inter_biUnion_flat (i : ι) (P T : Finset (∀ i, S i)) :
    (T ∩ P.biUnion (fun ω => flat {i} ω)).card =
      ∑ β ∈ P.image (proj i), (T ∩ fiber i β).card := by
  rw [biUnion_flat_eq, Finset.inter_biUnion, Finset.card_biUnion]
  intro β _ β' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  simp only [fiber, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact hne (hx.2.symm.trans hx'.2)

lemma card_flat_single (i : ι) (ω : ∀ i, S i) : (flat {i} ω).card = Fintype.card (S i) := by
  rw [card_flat, Finset.prod_singleton]

/-- lines inside `B` -/
lemma card_mul_image_le (i : ι) (P B : Finset (∀ i, S i)) (hP : ∀ ω ∈ P, flat {i} ω ⊆ B) :
    Fintype.card (S i) * (P.image (proj i)).card ≤ B.card := by
  have h := card_inter_biUnion_flat i P B
  have h2 : ∀ β ∈ P.image (proj i), (B ∩ fiber i β).card = Fintype.card (S i) := by
    intro β hβ
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.1 hβ
    rw [fiber_proj, Finset.inter_eq_right.2 (hP ω hω), card_flat_single]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at h
  rw [mul_comm, ← h]
  exact Finset.card_le_card Finset.inter_subset_left

/-- lines not inside a closed `B` -/
lemma card_out_lt {ρ : ℝ} {B : Finset (∀ i, S i)} (hB : IsClosedSet ρ B) (i : ι)
    (P : Finset (∀ i, S i)) (hP : ∀ ω ∈ P, ¬ flat {i} ω ⊆ B) :
    ((B ∩ P.biUnion (fun ω => flat {i} ω)).card : ℝ) ≤
        ρ * Fintype.card (S i) * (P.image (proj i)).card ∧
      (P.Nonempty → ((B ∩ P.biUnion (fun ω => flat {i} ω)).card : ℝ) <
        ρ * Fintype.card (S i) * (P.image (proj i)).card) := by
  rw [card_inter_biUnion_flat]
  push_cast
  have hterm : ∀ β ∈ P.image (proj i), ((B ∩ fiber i β).card : ℝ) < ρ * Fintype.card (S i) := by
    intro β hβ
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.1 hβ
    rw [fiber_proj]
    exact hB i ω (hP ω hω)
  have hconst : ρ * Fintype.card (S i) * ((P.image (proj i)).card : ℝ) =
      ∑ _β ∈ P.image (proj i), ρ * Fintype.card (S i) := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hconst]
  refine ⟨Finset.sum_le_sum fun β hβ => (hterm β hβ).le, fun hne => ?_⟩
  exact Finset.sum_lt_sum_of_nonempty (hne.image _) hterm

variable {F : Type} [Field F]

lemma mem_axisCode_iff (C : ∀ i, Submodule F (S i → F)) (i : ι) (x : (∀ i, S i) → F) :
    x ∈ axisCode C i ↔ ∀ b : (∀ i, S i), (fun t => x (Function.update b i t)) ∈ C i := by
  simp only [axisCode, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.funLeft_apply]
  exact Iff.rfl

lemma supportCard_eq {M : Type} [Zero M] (x : (∀ i, S i) → M) :
    supportCard x = (Finset.univ.filter fun ω => x ω ≠ 0).card := by
  unfold supportCard; congr 1

lemma lineCount_eq {M : Type} [Zero M] (i : ι) (x : (∀ i, S i) → M) :
    lineCount i x = ((Finset.univ.filter fun ω => x ω ≠ 0).image (proj i)).card := by
  unfold lineCount proj
  congr 1
  convert rfl

/-- inner part of a word along `i`-lines contained in `B` -/
noncomputable def inPart (B : Finset (∀ i, S i)) (i : ι) (z : (∀ i, S i) → F) :
    (∀ i, S i) → F :=
  fun ω => if flat {i} ω ⊆ B then z ω else 0

lemma inPart_mem {C : ∀ i, Submodule F (S i → F)} (B : Finset (∀ i, S i)) (i : ι)
    {z : (∀ i, S i) → F} (hz : z ∈ axisCode C i) : inPart B i z ∈ axisCode C i := by
  rw [mem_axisCode_iff] at hz ⊢
  intro b
  have : (fun t => inPart B i z (Function.update b i t)) =
      if flat {i} b ⊆ B then (fun t => z (Function.update b i t)) else 0 := by
    funext t
    simp only [inPart, flat_eq_of_mem (update_mem_flat b i t)]
    split_ifs <;> rfl
  rw [this]
  split_ifs
  · exact hz b
  · exact (C i).zero_mem

/-- **Lemma 17 of Kalachev–Panteleev**: closed sets are inner-generated. -/
theorem inner_generated {C : ∀ i, Submodule F (S i → F)} {ρ : ℝ}
    (hPE : IsProductExpanding ρ C) {B : Finset (∀ i, S i)} (hB : IsClosedSet ρ B) :
    ∀ n : ℕ, ∀ x ∈ ⨆ i, axisCode C i, supportCard x ≤ n → (∀ ω, x ω ≠ 0 → ω ∈ B) →
      ∃ y : ι → ((∀ i, S i) → F), (∀ i, y i ∈ axisCode C i) ∧
        (∀ i ω, y i ω ≠ 0 → flat {i} ω ⊆ B) ∧ x = ∑ i, y i := by
  intro n
  induction n with
  | zero =>
    intro x _ hx _
    refine ⟨0, fun i => Submodule.zero_mem _, fun i ω h => absurd rfl h, ?_⟩
    rw [supportCard_eq, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hx
    funext ω
    simp only [Pi.zero_apply, Finset.sum_const_zero]
    by_contra h
    exact hx (Finset.mem_univ ω) h
  | succ n ih =>
    intro x hx hwt hsupp
    obtain ⟨z, hz, hxz, hbound⟩ := hPE.2 x hx
    set zin : ι → ((∀ i, S i) → F) := fun i => inPart B i (z i) with hzin
    set zout : ι → ((∀ i, S i) → F) := fun i => z i - zin i with hzout
    have hzin_mem : ∀ i, zin i ∈ axisCode C i := fun i => inPart_mem B i (hz i)
    have hzin_supp : ∀ i ω, zin i ω ≠ 0 → flat {i} ω ⊆ B := by
      intro i ω h
      by_contra h'
      exact h (by simp [hzin, inPart, h'])
    have hsplit : x = ∑ i, zin i + ∑ i, zout i := by
      rw [← Finset.sum_add_distrib, hxz]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hzout]
    by_cases hall : ∀ i ω, zout i ω = 0
    · refine ⟨zin, hzin_mem, hzin_supp, ?_⟩
      have : ∑ i, zout i = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        funext ω; exact hall i ω
      rw [hsplit, this, add_zero]
    push Not at hall
    obtain ⟨i₀, ω₀, hω₀⟩ := hall
    set x'' := ∑ i, zout i with hx''
    have hx''_mem : x'' ∈ ⨆ i, axisCode C i :=
      Submodule.sum_mem _ fun i _ =>
        Submodule.mem_iSup_of_mem i (Submodule.sub_mem _ (hz i) (hzin_mem i))
    have hx''_supp : ∀ ω, x'' ω ≠ 0 → ω ∈ B := by
      intro ω hω
      by_contra hωB
      apply hω
      have hx0 : x ω = 0 := by
        by_contra h; exact hωB (hsupp ω h)
      have hin0 : (∑ i, zin i) ω = 0 := by
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_contra h
        exact hωB (hzin_supp i ω h (self_mem_flat _ _))
      have : x'' = x - ∑ i, zin i := by rw [hsplit]; ring
      rw [this, Pi.sub_apply, hx0, hin0, sub_zero]
    -- the weight bound
    set P : ι → Finset (∀ i, S i) := fun i => Finset.univ.filter fun ω => zout i ω ≠ 0 with hP
    have hPout : ∀ i, ∀ ω ∈ P i, ¬ flat {i} ω ⊆ B := by
      intro i ω hω hfl
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hω
      apply hω
      simp [hzout, hzin, inPart, hfl]
    have hPsub : ∀ i, P i ⊆ Finset.univ.filter fun ω => z i ω ≠ 0 := by
      intro i ω hω
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      intro h
      apply hω
      simp [hzout, hzin, inPart, h]
    have hsuppx'' : (Finset.univ.filter fun ω => x'' ω ≠ 0) ⊆
        Finset.univ.biUnion fun i => B ∩ (P i).biUnion (fun ω => flat {i} ω) := by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      have hωB := hx''_supp ω hω
      rw [hx'', Finset.sum_apply] at hω
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hω
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ _, Finset.mem_inter.2 ⟨hωB, ?_⟩⟩
      rw [Finset.mem_biUnion]
      exact ⟨ω, by simpa [hP] using hi, self_mem_flat _ _⟩
    have hlt : (supportCard x'' : ℝ) < supportCard x := by
      calc (supportCard x'' : ℝ)
          ≤ ∑ i, ((B ∩ (P i).biUnion (fun ω => flat {i} ω)).card : ℝ) := by
            rw [supportCard_eq]
            exact_mod_cast (Finset.card_le_card hsuppx'').trans Finset.card_biUnion_le
        _ < ∑ i, ρ * Fintype.card (S i) * ((P i).image (proj i)).card := by
            apply Finset.sum_lt_sum
            · intro i _; exact (card_out_lt hB i (P i) (hPout i)).1
            · refine ⟨i₀, Finset.mem_univ _, (card_out_lt hB i₀ (P i₀) (hPout i₀)).2 ?_⟩
              exact ⟨ω₀, by simpa [hP] using hω₀⟩
        _ ≤ ∑ i, ρ * Fintype.card (S i) * (lineCount i (z i) : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hρ : 0 ≤ ρ := hPE.1.le
            gcongr
            rw [lineCount_eq]
            exact Finset.card_le_card (Finset.image_subset_image (hPsub i))
        _ = ρ * ∑ i, (Fintype.card (S i) : ℝ) * (lineCount i (z i) : ℝ) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ supportCard x := hbound
    have hwt'' : supportCard x'' ≤ n := by
      have : (supportCard x'' : ℝ) < n + 1 := by
        calc (supportCard x'' : ℝ) < supportCard x := hlt
          _ ≤ n + 1 := by exact_mod_cast hwt
      have : supportCard x'' < n + 1 := by exact_mod_cast this
      omega
    obtain ⟨w, hw, hwsupp, hx''w⟩ := ih x'' hx''_mem hwt'' hx''_supp
    refine ⟨fun i => zin i + w i, fun i => Submodule.add_mem _ (hzin_mem i) (hw i), ?_, ?_⟩
    · intro i ω h
      by_cases h1 : zin i ω = 0
      · simp only [Pi.add_apply, h1, zero_add] at h
        exact hwsupp i ω h
      · exact hzin_supp i ω h1
    · rw [Finset.sum_add_distrib, ← hx''w]
      exact hsplit

end PrivPCP.Lemma48Aux


namespace PrivPCP.L49

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]

lemma wtU_eq {A α : Type} [Fintype α] (X : A → α → F) :
    wtU X = (Finset.univ.filter fun ω => ∃ a, X a ω ≠ 0).card := by
  unfold wtU supportCard
  congr 1
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  constructor
  · intro h; by_contra h'; push Not at h'; exact h (funext h')
  · rintro ⟨a, ha⟩ h; exact ha (congrFun h a)

lemma wtU_triangle {A α : Type} [Fintype α] (X Y Z : A → α → F) :
    wtU (X - Z) ≤ wtU (X - Y) + wtU (Y - Z) := by
  rw [wtU_eq, wtU_eq, wtU_eq]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro ω hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.sub_apply] at hω ⊢
  obtain ⟨a, ha⟩ := hω
  by_contra h
  push Not at h
  apply ha
  have h1 := h.1 a; have h2 := h.2 a
  rw [sub_eq_zero] at h1 h2
  rw [h1, h2, sub_self]

lemma wtU_neg {A α : Type} [Fintype α] (X : A → α → F) : wtU (-X) = wtU X := by
  rw [wtU_eq, wtU_eq]; simp

lemma wtU_comm {A α : Type} [Fintype α] (X Y : A → α → F) : wtU (X - Y) = wtU (Y - X) := by
  rw [← neg_sub, wtU_neg]

noncomputable def distU {A α : Type} [Fintype α] (M : A → α → F) (E : Submodule F (α → F)) : ℕ :=
  sInf {d | ∃ Y : A → α → F, (∀ a, Y a ∈ E) ∧ wtU (M - Y) = d}

lemma exists_distU {A α : Type} [Fintype α] (M : A → α → F) (E : Submodule F (α → F)) :
    ∃ Y : A → α → F, (∀ a, Y a ∈ E) ∧ wtU (M - Y) = distU M E :=
  Nat.sInf_mem (s := {d | ∃ Y : A → α → F, (∀ a, Y a ∈ E) ∧ wtU (M - Y) = d})
    ⟨_, 0, fun _ => E.zero_mem, rfl⟩

lemma distU_le {A α : Type} [Fintype α] (M : A → α → F) (E : Submodule F (α → F))
    (Y : A → α → F) (hY : ∀ a, Y a ∈ E) : distU M E ≤ wtU (M - Y) :=
  Nat.sInf_le ⟨Y, hY, rfl⟩

/-- decomposition of a member of a finite supremum -/
lemma exists_decomp {ι α : Type} [Fintype ι] (p : ι → Submodule F (α → F)) (x : α → F)
    (hx : x ∈ ⨆ i, p i) : ∃ f : ι → α → F, (∀ i, f i ∈ p i) ∧ x = ∑ i, f i := by
  refine Submodule.iSup_induction p (motive := fun x => ∃ f : ι → α → F, (∀ i, f i ∈ p i) ∧
    x = ∑ i, f i) hx ?_ ?_ ?_
  · intro i y hy
    refine ⟨Pi.single i y, fun j => ?_, ?_⟩
    · by_cases h : j = i
      · subst h; simpa using hy
      · simp [Pi.single_apply, h]
    · rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp
  · exact ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
  · rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, fun i => Submodule.add_mem _ (hf i) (hg i), by
      rw [← Finset.sum_add_distrib]; rfl⟩

end PrivPCP.L49


namespace PrivPCP.L49

open GoodQLTC Classical

variable {F : Type} [Field F]

/-- Lemma 4.8 for an arbitrary finite index type -/
theorem cpe_generic {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
    (hι : 0 < Fintype.card ι) (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1) (C : ∀ i, Submodule F (S i → F))
    (hPE : IsProductExpanding ρ C) :
    IsCollectivelyPE (ρ ^ Fintype.card ι / (Fintype.card ι * (2 ^ Fintype.card ι + 1) ^ Fintype.card ι)) C := by
  intro A _ X hX
  set r := Fintype.card ι with hr
  set Asupp : Finset (∀ i, S i) := Finset.univ.filter fun ω => (fun a => X a ω) ≠ 0 with hAsupp
  set B := Lemma48Aux.closureSet (ρ / 2 ^ r) Asupp with hB
  have hBc : Lemma48Aux.IsClosedSet ρ B := Lemma48Aux.closureSet_closed hρ.1 Asupp
  have hcard : (B.card : ℝ) ≤ ((2 ^ r + 1) / ρ) ^ r * Asupp.card :=
    Lemma48Aux.closureSet_card (S := S) hρ.1 hρ.2 Asupp
  have hρ0 := hρ.1
  have hex : ∀ a, ∃ y : ι → ((∀ i, S i) → F), (∀ i, y i ∈ axisCode C i) ∧
      (∀ i ω, y i ω ≠ 0 → Lemma48Aux.flat {i} ω ⊆ B) ∧ X a = ∑ i, y i := by
    intro a
    refine Lemma48Aux.inner_generated hPE hBc (supportCard (X a)) (X a) (hX a) le_rfl ?_
    intro ω hω
    apply Lemma48Aux.subset_closureSet
    simp only [hAsupp, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    exact hω (congrFun h a)
  choose Y hY1 hY2 hY3 using hex
  refine ⟨Y, hY1, hY3, ?_⟩
  have hline : ∀ i, (Fintype.card (S i) : ℝ) * (lineCountU i (fun a => Y a i) : ℝ) ≤ B.card := by
    intro i
    unfold lineCountU
    rw [Lemma48Aux.lineCount_eq]
    have := Lemma48Aux.card_mul_image_le i
      (Finset.univ.filter fun ω => (fun a => Y a i ω) ≠ 0) B ?_
    · exact_mod_cast this
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hω
      exact hY2 a i ω ha
  have hwt : (wtU X : ℝ) = Asupp.card := by
    unfold wtU; rw [Lemma48Aux.supportCard_eq, hAsupp]
    norm_cast
  have hP : 0 ≤ ρ ^ r / (r * (2 ^ r + 1) ^ r) := by positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hι
  calc ρ ^ r / (r * (2 ^ r + 1) ^ r) *
        ∑ i, (Fintype.card (S i) : ℝ) * (lineCountU i (fun a => Y a i) : ℝ)
      ≤ ρ ^ r / (r * (2 ^ r + 1) ^ r) * ∑ _i : ι, (B.card : ℝ) := by
        gcongr with i
        exact hline i
    _ = ρ ^ r / (r * (2 ^ r + 1) ^ r) * r * B.card := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ρ ^ r / (r * (2 ^ r + 1) ^ r) * r * (((2 ^ r + 1) / ρ) ^ r * Asupp.card) := by
        gcongr
    _ = Asupp.card := by
        have : (0 : ℝ) < ρ ^ r := by positivity
        have : (0 : ℝ) < 2 ^ r + 1 := by positivity
        field_simp
        rw [div_pow, mul_div_assoc', mul_div_right_comm, div_self (by positivity), one_mul]
    _ = wtU X := hwt.symm

lemma cpe_mono {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
    (C : ∀ i, Submodule F (S i → F)) (P P' : ℝ) (hP' : 0 ≤ P') (hPP : P' ≤ P)
    (h : IsCollectivelyPE P C) : IsCollectivelyPE P' C := by
  intro A _ X hX
  obtain ⟨Y, h1, h2, h3⟩ := h A X hX
  refine ⟨Y, h1, h2, le_trans ?_ h3⟩
  exact mul_le_mul_of_nonneg_right hPP (Finset.sum_nonneg fun i _ => by positivity)

end PrivPCP.L49


namespace PrivPCP.L49

open GoodQLTC Classical

variable {F : Type} [Field F]

lemma quot_basis {α : Type} [Fintype α] (U W : Submodule F (α → F)) (hUW : U ≤ W) :
    ∃ (d : ℕ) (u h : Fin d → α → F), (∀ s, h s ∈ W) ∧ (∀ s, ∀ v ∈ U, u s ⬝ᵥ v = 0) ∧
      (∀ w ∈ W, w - ∑ s, (u s ⬝ᵥ w) • h s ∈ U) := by
  set N := U.comap W.subtype with hN
  let bQ := Module.finBasis F (W ⧸ N)
  set d := Module.finrank F (W ⧸ N)
  have hsurj : ∀ s : Fin d, ∃ w : W, N.mkQ w = bQ s := fun s => Submodule.mkQ_surjective N (bQ s)
  choose hw hhw using hsurj
  have hext : ∀ s : Fin d, ∃ g : (α → F) →ₗ[F] F, g.comp W.subtype = (bQ.coord s).comp N.mkQ :=
    fun s => LinearMap.exists_extend _
  choose g hg using hext
  have hgdot : ∀ s v, g s v = (fun x => g s (Pi.single x 1)) ⬝ᵥ v :=
    fun s v => L46Aux.functional_eq_dot' (g s) v
  refine ⟨d, fun s x => g s (Pi.single x 1), fun s => (hw s : α → F), fun s => (hw s).2, ?_, ?_⟩
  · intro s v hv
    rw [← hgdot]
    have := congrArg (fun f => f ⟨v, hUW hv⟩) (hg s)
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [this]
    have h0 : N.mkQ ⟨v, hUW hv⟩ = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN, Submodule.mem_comap]
      exact hv
    rw [h0, map_zero]
  · intro w hwW
    have key : N.mkQ (⟨w, hwW⟩ - ∑ s, (bQ.coord s (N.mkQ ⟨w, hwW⟩)) • hw s) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, hhw]
      rw [sub_eq_zero]
      exact (bQ.sum_repr _).symm
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at key
    have key2 : (⟨w, hwW⟩ - ∑ s, (bQ.coord s (N.mkQ ⟨w, hwW⟩)) • hw s : W) ∈ U.comap W.subtype := key
    rw [Submodule.mem_comap] at key2
    convert key2 using 1
    simp only [Submodule.coe_subtype, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [← hgdot]
    have := congrArg (fun f => f ⟨w, hwW⟩) (hg s)
    simpa using this

end PrivPCP.L49


namespace PrivPCP.L49

open GoodQLTC Classical PrivPCP.TDual PrivPCP.L46Aux

variable {F : Type} [Field F]

section generic
variable {κ : Type} [Fintype κ] [DecidableEq κ] {T : κ → Type} [∀ i, Fintype (T i)]
variable (Y : NestedCodes F κ T)

/-- the dual family of `E_i` -/
def famD (i : κ) : ∀ j, Submodule F (T j → F) :=
  fun j => dualCode (Function.update Y.V i (Y.K i) j)

lemma famD_self (i : κ) : famD Y i i = Y.W i := by
  simp [famD, NestedCodes.W]

lemma famD_ne (i j : κ) (h : j ≠ i) : famD Y i j = Y.U j := by
  simp [famD, NestedCodes.U, Function.update_of_ne h]

lemma D_eq (i : κ) : Y.D i = ⨆ j, axisCode (famD Y i) j := dualE_eq Y i

lemma Dbig_eq : Y.Dbig = ⨅ i, Y.D i := dualCode_iSup Y.E

lemma U_le_W (hKV : ∀ i, Y.K i ≤ Y.V i) (j : κ) : Y.U j ≤ Y.W j := dualCode_antitone (hKV j)

lemma axisU_le_D (i j : κ) (h : j ≠ i) : axisCode Y.U j ≤ Y.D i := by
  rw [D_eq, axisCode_congr Y.U (famD Y i) j (famD_ne Y i j h).symm]
  exact le_iSup (fun j => axisCode (famD Y i) j) j

lemma axisW_le_D (i : κ) : axisCode Y.W i ≤ Y.D i := by
  rw [D_eq, axisCode_congr Y.W (famD Y i) i (famD_self Y i).symm]
  exact le_iSup (fun j => axisCode (famD Y i) j) i

lemma B_le_D (hKV : ∀ i, Y.K i ≤ Y.V i) (i : κ) : Y.B ≤ Y.D i := by
  rw [B_eq]
  apply iSup_le
  intro j
  by_cases h : j = i
  · subst h
    exact (axisCode_mono Y.U Y.W j (U_le_W Y hKV j)).trans (axisW_le_D Y j)
  · exact axisU_le_D Y i j h

end generic

end PrivPCP.L49


namespace PrivPCP.L49

open GoodQLTC Classical PrivPCP.TDual PrivPCP.L46Aux

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

abbrev lift {I : Finset ι} {t : ι} (j : {i // i ∈ I.erase t}) : {i // i ∈ I} :=
  ⟨j.val, Finset.mem_of_mem_erase j.2⟩

lemma lift_ne_tpt {I : Finset ι} {t : ι} (ht : t ∈ I) (j : {i // i ∈ I.erase t}) :
    lift j ≠ tpt ht := by
  intro h; exact Finset.ne_of_mem_erase j.2 (congrArg Subtype.val h)

lemma famD_code_eq {I : Finset ι} {t : ι} (i j : {i // i ∈ I.erase t}) :
    famD (X.restrict I) (lift i) (lift j) = famD (X.restrict (I.erase t)) i j := by
  by_cases h : j = i
  · subst h; rw [famD_self, famD_self]; rfl
  · have h' : lift j ≠ lift i := by
      intro e; apply h; apply Subtype.ext; have := congrArg Subtype.val e; simpa using this
    rw [famD_ne _ _ _ h', famD_ne _ _ _ h]; rfl

lemma contr_add {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (z z' : Om S I → F) :
    contr ht u (z + z') = contr ht u z + contr ht u z' := by
  funext y; simp [contr, mul_add, Finset.sum_add_distrib]

lemma contr_zero {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) :
    contr ht u (0 : Om S I → F) = 0 := by
  funext y; simp [contr]

lemma contr_line_ne {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (z : Om S I → F)
    (j : {i // i ∈ I.erase t}) (Cj : Submodule F (S j.val → F))
    (hz : ∀ b, (fun s => z (Function.update b (lift j) s)) ∈ Cj) (y : Om S (I.erase t)) :
    (fun s => contr ht u z (Function.update y j s)) ∈ Cj := by
  have : (fun s => contr ht u z (Function.update y j s)) =
      ∑ x, u x • (fun s => z (Function.update (ext ht x y) (lift j) s)) := by
    funext s
    simp only [contr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [update_ext_ne]
  rw [this]
  exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hz _)

lemma contr_U_zero {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F)
    (hu : ∀ v ∈ X.U t, u ⬝ᵥ v = 0) (z : Om S I → F)
    (hz : z ∈ axisCode (X.restrict I).U (tpt ht)) : contr ht u z = 0 := by
  funext y
  by_cases hS : Nonempty (S t)
  · obtain ⟨s0⟩ := hS
    rw [mem_axisCode_iff] at hz
    have hl := hz (ext ht s0 y)
    have : contr ht u z y = u ⬝ᵥ (fun s => z (Function.update (ext ht s0 y) (tpt ht) s)) := by
      simp only [contr, dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← ext_eq_update, res_ext]
    rw [this]
    exact hu _ hl
  · simp only [contr, Pi.zero_apply]
    rw [not_nonempty_iff] at hS
    simp [Finset.univ_eq_empty]

lemma contr_mem_D {I : Finset ι} {t : ι} (ht : t ∈ I) (i : {i // i ∈ I.erase t}) (u : S t → F)
    (hu : ∀ v ∈ X.U t, u ⬝ᵥ v = 0) (z : Om S I → F) (hz : z ∈ (X.restrict I).D (lift i)) :
    contr ht u z ∈ (X.restrict (I.erase t)).D i := by
  rw [D_eq] at hz
  refine Submodule.iSup_induction _ (motive := fun z => contr ht u z ∈ (X.restrict (I.erase t)).D i)
    hz ?_ ?_ ?_
  · intro j z hzj
    by_cases hj : j = tpt ht
    · subst hj
      rw [axisCode_congr _ (X.restrict I).U (tpt ht)
        (famD_ne _ _ _ (fun e => lift_ne_tpt ht i e.symm))] at hzj
      rw [contr_U_zero X ht u hu z hzj]; exact Submodule.zero_mem _
    · have hjt : j.val ≠ t := fun e => hj (Subtype.ext e)
      let jj : {i // i ∈ I.erase t} := ⟨j.val, Finset.mem_erase.2 ⟨hjt, j.2⟩⟩
      have hjj : j = lift jj := Subtype.ext rfl
      rw [D_eq]
      apply Submodule.mem_iSup_of_mem jj
      rw [mem_axisCode_iff]
      intro y
      rw [mem_axisCode_iff] at hzj
      rw [hjj] at hzj
      rw [← famD_code_eq X i jj]
      exact contr_line_ne ht u z jj _ hzj y
  · rw [contr_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [contr_add]; exact Submodule.add_mem _ ha hb

lemma tl_mem_D {I : Finset ι} {t : ι} (ht : t ∈ I) (i : {i // i ∈ I.erase t}) (h : S t → F)
    (P : Om S (I.erase t) → F) (hP : P ∈ (X.restrict (I.erase t)).D i) :
    tl ht h P ∈ (X.restrict I).D (lift i) := by
  rw [D_eq] at hP
  refine Submodule.iSup_induction _ (motive := fun P => tl ht h P ∈ (X.restrict I).D (lift i))
    hP ?_ ?_ ?_
  · intro jj P hPj
    rw [D_eq]
    apply Submodule.mem_iSup_of_mem (lift jj)
    rw [mem_axisCode_iff] at hPj ⊢
    intro b
    rw [famD_code_eq X i jj]
    exact tl_line_ne ht h P jj _ hPj b
  · rw [tl_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [tl_add]; exact Submodule.add_mem _ ha hb

lemma tl_mem_Dt {I : Finset ι} {t : ι} (ht : t ∈ I) (h : S t → F) (hh : h ∈ X.W t)
    (P : Om S (I.erase t) → F) : tl ht h P ∈ (X.restrict I).D (tpt ht) := by
  apply axisW_le_D
  rw [mem_axisCode_iff]
  intro b
  exact tl_line_t ht h P (X.W t) hh b

lemma linefix {I : Finset ι} {t : ι} (ht : t ∈ I) {d : ℕ} (u h : Fin d → S t → F)
    (hh : ∀ w ∈ X.W t, w - ∑ s, (u s ⬝ᵥ w) • h s ∈ X.U t) (w : Om S I → F)
    (hw : w ∈ axisCode (X.restrict I).W (tpt ht)) :
    w - ∑ s, tl ht (h s) (contr ht (u s) w) ∈ axisCode (X.restrict I).U (tpt ht) := by
  rw [mem_axisCode_iff] at hw ⊢
  intro b
  have hl := hh _ (hw b)
  change (fun x => (w - ∑ s, tl ht (h s) (contr ht (u s) w)) (Function.update b (tpt ht) x)) ∈ X.U t
  have heq : (fun x => (w - ∑ s, tl ht (h s) (contr ht (u s) w)) (Function.update b (tpt ht) x)) =
      (fun x => w (Function.update b (tpt ht) x)) -
        ∑ s, (u s ⬝ᵥ fun x => w (Function.update b (tpt ht) x)) • h s := by
    funext x
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tl]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [update_t_at, res_update_t, ← line_dot_contr, mul_comm]
  rw [heq]; exact hl

end PrivPCP.L49


namespace PrivPCP.L49

open GoodQLTC Classical PrivPCP.TDual PrivPCP.L46Aux

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

lemma wt_contr_fam {I : Finset ι} {t : ι} (ht : t ∈ I) {A : Type} [Fintype A] {d : ℕ}
    (u : Fin d → S t → F) (Xf : A → Om S I → F) :
    wtU (fun p : A × Fin d => contr ht (u p.2) (Xf p.1)) ≤ lineCountU (tpt ht) Xf := by
  rw [wtU_eq]
  unfold lineCountU
  rw [Lemma48Aux.lineCount_eq]
  let f : Om S (I.erase t) → ((j : {j : {i // i ∈ I} // j ≠ tpt ht}) → S j.1.val) :=
    fun y j => y ⟨j.1.val, Finset.mem_erase.2 ⟨fun h => j.2 (Subtype.ext h), j.1.2⟩⟩
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy
    obtain ⟨⟨a, s⟩, hp⟩ := hy
    obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    have hx' : Xf a (ext ht x y) ≠ 0 := right_ne_zero_of_mul hx
    simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
      Set.mem_setOf_eq]
    refine ⟨ext ht x y, fun h => hx' (congrFun h a), ?_⟩
    funext j
    exact ext_ne ht x y j.1 (fun h => j.2 (Subtype.ext h))
  · intro y _ y' _ hyy
    funext jJ
    have := congrFun hyy ⟨⟨jJ.val, Finset.mem_of_mem_erase jJ.2⟩,
      fun h => Finset.ne_of_mem_erase jJ.2 (congrArg Subtype.val h)⟩
    simpa [f] using this

lemma card_res_preimage {I : Finset ι} {t : ι} (ht : t ∈ I) (T : Finset (Om S (I.erase t))) :
    (Finset.univ.filter fun ω : Om S I => res ht ω ∈ T).card = Fintype.card (S t) * T.card := by
  rw [Finset.card_filter]
  rw [← Fintype.sum_equiv (extEquiv ht) (fun p => if res ht (ext ht p.1 p.2) ∈ T then 1 else 0)
    _ (fun p => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [res_ext]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.card_filter]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

lemma wt_tl_fam {I : Finset ι} {t : ι} (ht : t ∈ I) {A : Type} [Fintype A] {d : ℕ}
    (h : Fin d → S t → F) (c : A × Fin d → Om S (I.erase t) → F) :
    wtU (fun a => ∑ s, tl ht (h s) (c (a, s))) ≤ Fintype.card (S t) * wtU c := by
  rw [wtU_eq, wtU_eq, ← card_res_preimage ht]
  apply Finset.card_le_card
  intro ω hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  obtain ⟨a, ha⟩ := hω
  rw [Finset.sum_apply] at ha
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  exact ⟨(a, s), right_ne_zero_of_mul hs⟩

end PrivPCP.L49


namespace PrivPCP.L49

open GoodQLTC Classical PrivPCP.TDual PrivPCP.L46Aux

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

/-- relative robust testability at level `I` with constant `K` (collective form) -/
def RT (I : Finset ι) (K : ℝ) : Prop :=
  ∀ (A : Type) [Fintype A] (M : A → Om S I → F), ∃ Q : A → Om S I → F,
    (∀ a, Q a ∈ (X.restrict I).Dbig) ∧
      (wtU (M - Q) : ℝ) ≤ K * ∑ i, (distU M ((X.restrict I).D i) : ℝ)

lemma tl_sub {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P P' : Om S (I.erase t) → F) :
    tl ht u (P - P') = tl ht u P - tl ht u P' := by funext ω; simp [tl, mul_sub]

lemma sum_split {I : Finset ι} {t : ι} (ht : t ∈ I) (f : {i // i ∈ I} → ℝ) :
    ∑ j, f j = f (tpt ht) + ∑ i : {i // i ∈ I.erase t}, f (lift i) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (tpt ht))]
  congr 1
  symm
  refine Finset.sum_bij (fun i _ => lift i) ?_ ?_ ?_ ?_
  · intro i _; simp [lift_ne_tpt ht i]
  · intro i _ i' _ h; apply Subtype.ext; have := congrArg Subtype.val h; simpa using this
  · intro j hj
    have hjt : j.val ≠ t := fun e => (Finset.ne_of_mem_erase hj) (Subtype.ext e)
    exact ⟨⟨j.val, Finset.mem_erase.2 ⟨hjt, j.2⟩⟩, Finset.mem_univ _, rfl⟩
  · intro i _; rfl

lemma card_J {I : Finset ι} {t : ι} (ht : t ∈ I) :
    Fintype.card {i // i ∈ I.erase t} = I.card - 1 := by
  rw [Fintype.card_coe, Finset.card_erase_of_mem ht]

end PrivPCP.L49


namespace PrivPCP.L49

open GoodQLTC Classical PrivPCP.TDual PrivPCP.L46Aux

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

/-- the mixed tuple with `W` at `i` and `t` and `U` elsewhere -/
abbrev mix2 (I : Finset ι) (t i : ι) : ∀ j : {j // j ∈ I}, Submodule F (S j.val → F) :=
  (X.restrict I).mixed (fun j => decide (j.val ≠ i ∧ j.val ≠ t))

lemma famD_le_mix2 (hKV : ∀ i, X.K i ≤ X.V i) {I : Finset ι} {t : ι} (ht : t ∈ I)
    (i : {i // i ∈ I.erase t}) (c : {i // i ∈ I}) (hc : c = lift i ∨ c = tpt ht)
    (j : {j // j ∈ I}) : famD (X.restrict I) c j ≤ mix2 X I t i.val j := by
  by_cases hj : j = c
  · subst hj
    rw [famD_self]
    have : ¬ (j.val ≠ i.val ∧ j.val ≠ t) := by
      rcases hc with rfl | rfl
      · simp [lift]
      · simp [tpt]
    simp only [mix2, NestedCodes.mixed]; rw [if_neg (by simpa using this)]
  · rw [famD_ne _ _ _ hj]
    by_cases hb : j.val ≠ i.val ∧ j.val ≠ t
    · have : mix2 X I t i.val j = (X.restrict I).U j := by
        simp only [mix2, NestedCodes.mixed]; rw [if_pos (by simpa using hb)]
      rw [this]
    · have : mix2 X I t i.val j = (X.restrict I).W j := by
        simp only [mix2, NestedCodes.mixed]; rw [if_neg (by simpa using hb)]
      rw [this]; exact U_le_W (X.restrict I) (fun i => hKV i.val) j

lemma D_le_mix2 (hKV : ∀ i, X.K i ≤ X.V i) {I : Finset ι} {t : ι} (ht : t ∈ I)
    (i : {i // i ∈ I.erase t}) (c : {i // i ∈ I}) (hc : c = lift i ∨ c = tpt ht) :
    (X.restrict I).D c ≤ ⨆ j, axisCode (mix2 X I t i.val) j := by
  rw [D_eq]
  exact iSup_mono fun j => axisCode_mono _ _ j (famD_le_mix2 X hKV ht i c hc j)

end PrivPCP.L49


namespace PrivPCP.L49

open GoodQLTC Classical PrivPCP.TDual PrivPCP.L46Aux

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

theorem step49 (hKV : ∀ i, X.K i ≤ X.V i) (I : Finset ι) (t : ι) (ht : t ∈ I)
    (P K' : ℝ) (hP : 0 < P) (hK' : 0 ≤ K')
    (hCPE : ∀ i : {i // i ∈ I.erase t}, IsCollectivelyPE P (mix2 X I t i.val))
    (IH : RT X (I.erase t) K') :
    RT X I (1 + ((I.card - 1 : ℕ) : ℝ) * K' / P) := by
  intro A _ M
  have hKVI : ∀ i, (X.restrict I).K i ≤ (X.restrict I).V i := fun i => hKV i.val
  -- nearest codewords
  have hY : ∀ i, ∃ Y : A → Om S I → F, (∀ a, Y a ∈ (X.restrict I).D i) ∧
      wtU (M - Y) = distU M ((X.restrict I).D i) := fun i => exists_distU _ _
  choose Y hYD hYw using hY
  set tt : {i // i ∈ I} → ℕ := fun i => distU M ((X.restrict I).D i) with htt
  set Yt := Y (tpt ht) with hYt
  -- pairwise repairs
  have hpair : ∀ i : {i // i ∈ I.erase t}, ∃ W2 : A → {j // j ∈ I} → Om S I → F,
      (∀ a j, W2 a j ∈ axisCode (mix2 X I t i.val) j) ∧
      (∀ a, Y (lift i) a - Yt a = ∑ j, W2 a j) ∧
      P * ∑ j, (Fintype.card (S j.val) : ℝ) * (lineCountU j (fun a => W2 a j) : ℝ) ≤
        wtU (fun a => Y (lift i) a - Yt a) := by
    intro i
    apply hCPE i A
    intro a
    exact Submodule.sub_mem _ (D_le_mix2 X hKV ht i _ (Or.inl rfl) (hYD _ a))
      (D_le_mix2 X hKV ht i _ (Or.inr rfl) (hYD _ a))
  choose W2 hW2ax hW2sum hW2bd using hpair
  let Xi : {i // i ∈ I.erase t} → A → Om S I → F := fun i a => W2 i a (tpt ht)
  let lam : {i // i ∈ I.erase t} → ℕ := fun i => lineCountU (tpt ht) (Xi i)
  have hlam : ∀ i, P * Fintype.card (S t) * lam i ≤ tt (lift i) + tt (tpt ht) := by
    intro i
    have h1 := hW2bd i
    have h2 : (Fintype.card (S t) : ℝ) * (lam i : ℝ) ≤
        ∑ j, (Fintype.card (S j.val) : ℝ) * (lineCountU j (fun a => W2 i a j) : ℝ) :=
      Finset.single_le_sum (f := fun j => (Fintype.card (S j.val) : ℝ) *
        (lineCountU j (fun a => W2 i a j) : ℝ)) (fun j _ => by positivity) (Finset.mem_univ (tpt ht))
    have h3 : wtU (fun a => Y (lift i) a - Yt a) ≤ tt (lift i) + tt (tpt ht) := by
      have := wtU_triangle (Y (lift i)) M Yt
      rw [wtU_comm (Y (lift i)) M] at this
      have e1 : wtU (M - Y (lift i)) = tt (lift i) := hYw _
      have e2 : wtU (M - Yt) = tt (tpt ht) := hYw _
      have : (fun a => Y (lift i) a - Yt a) = Y (lift i) - Yt := rfl
      rw [this]; omega
    calc P * Fintype.card (S t) * lam i = P * ((Fintype.card (S t) : ℝ) * (lam i : ℝ)) := by ring
      _ ≤ P * ∑ j, (Fintype.card (S j.val) : ℝ) * (lineCountU j (fun a => W2 i a j) : ℝ) :=
          mul_le_mul_of_nonneg_left h2 hP.le
      _ ≤ _ := h1
      _ ≤ _ := by exact_mod_cast h3
  -- `Yt + Xi` lies in `D_i`
  have hYX : ∀ i a, Yt a + Xi i a ∈ (X.restrict I).D (lift i) := by
    intro i a
    have hsum := hW2sum i a
    have : Yt a + Xi i a = Y (lift i) a - ∑ j ∈ Finset.univ.erase (tpt ht), W2 i a j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (tpt ht))] at hsum
      simp only [Xi]
      rw [sub_eq_iff_eq_add] at hsum
      rw [hsum]; abel
    rw [this]
    refine Submodule.sub_mem _ (hYD _ a) (Submodule.sum_mem _ fun j hj => ?_)
    have hjt : j ≠ tpt ht := Finset.ne_of_mem_erase hj
    have hax := hW2ax i a j
    by_cases hji : j = lift i
    · subst hji
      apply axisW_le_D
      rw [axisCode_congr _ (X.restrict (I)).W (lift i) (by
        simp [NestedCodes.mixed, lift])] at hax
      exact hax
    · have hb : j.val ≠ i.val ∧ j.val ≠ t := ⟨fun e => hji (Subtype.ext e),
        fun e => hjt (Subtype.ext e)⟩
      apply axisU_le_D _ _ _ hji
      rw [axisCode_congr _ (X.restrict I).U j (by simp [NestedCodes.mixed, hb])] at hax
      exact hax
  -- decomposition of `Yt`
  have hdec : ∀ a, ∃ f : {j // j ∈ I} → Om S I → F,
      (∀ j, f j ∈ axisCode (famD (X.restrict I) (tpt ht)) j) ∧ Yt a = ∑ j, f j := by
    intro a
    have := hYD (tpt ht) a
    rw [D_eq] at this
    exact exists_decomp _ _ this
  choose fY hfY hfYsum using hdec
  let bb : A → Om S I → F := fun a => ∑ j ∈ Finset.univ.erase (tpt ht), fY a j
  let ww : A → Om S I → F := fun a => fY a (tpt ht)
  have hYbw : ∀ a, Yt a = bb a + ww a := by
    intro a; rw [hfYsum a, ← Finset.add_sum_erase _ _ (Finset.mem_univ (tpt ht))]; abel
  have hbB : ∀ a, bb a ∈ (X.restrict I).B := by
    intro a
    refine Submodule.sum_mem _ fun j hj => ?_
    have hjt : j ≠ tpt ht := Finset.ne_of_mem_erase hj
    rw [B_eq]
    apply Submodule.mem_iSup_of_mem j
    have := hfY a j
    rwa [axisCode_congr _ (X.restrict I).U j (famD_ne _ _ _ hjt)] at this
  have hwW : ∀ a, ww a ∈ axisCode (X.restrict I).W (tpt ht) := by
    intro a
    have := hfY a (tpt ht)
    rwa [axisCode_congr _ (X.restrict I).W (tpt ht) (famD_self _ _)] at this
  -- quotient basis of `W_t / U_t`
  obtain ⟨d, u, h, hhW, huU, hfix⟩ := quot_basis (X.U t) (X.W t) (U_le_W X hKV t)
  -- the coefficient family
  let m : A × Fin d → Om S (I.erase t) → F := fun p => contr ht (u p.2) (ww p.1)
  let xx : {i // i ∈ I.erase t} → A × Fin d → Om S (I.erase t) → F :=
    fun i p => contr ht (u p.2) (Xi i p.1)
  have hmx : ∀ i p, m p + xx i p ∈ (X.restrict (I.erase t)).D i := by
    intro i p
    simp only [m, xx]
    rw [← contr_add]
    apply contr_mem_D X ht i (u p.2) (huU p.2)
    have : ww p.1 + Xi i p.1 = (Yt p.1 + Xi i p.1) - bb p.1 := by rw [hYbw]; abel
    rw [this]
    exact Submodule.sub_mem _ (hYX i p.1) (B_le_D _ hKVI _ (hbB p.1))
  have hdist : ∀ i, distU m ((X.restrict (I.erase t)).D i) ≤ lam i := by
    intro i
    refine (distU_le m _ (fun p => m p + xx i p) (hmx i)).trans ?_
    have : m - (fun p => m p + xx i p) = -(xx i) := by funext p; simp
    rw [this, wtU_neg]
    exact wt_contr_fam ht u (Xi i)
  -- the induction hypothesis
  obtain ⟨q, hqD, hqw⟩ := IH (A × Fin d) m
  -- the repaired family
  let Q : A → Om S I → F := fun a => Yt a - ∑ s, tl ht (h s) (m (a, s) - q (a, s))
  refine ⟨Q, ?_, ?_⟩
  · intro a
    rw [Dbig_eq, Submodule.mem_iInf]
    intro j
    by_cases hj : j = tpt ht
    · subst hj
      exact Submodule.sub_mem _ (hYD _ a)
        (Submodule.sum_mem _ fun s _ => tl_mem_Dt X ht (h s) (hhW s) _)
    · have hjt : j.val ≠ t := fun e => hj (Subtype.ext e)
      let jj : {i // i ∈ I.erase t} := ⟨j.val, Finset.mem_erase.2 ⟨hjt, j.2⟩⟩
      have hjj : j = lift jj := Subtype.ext rfl
      have hQ : Q a = bb a + (ww a - ∑ s, tl ht (h s) (m (a, s))) +
          ∑ s, tl ht (h s) (q (a, s)) := by
        simp only [Q, tl_sub, Finset.sum_sub_distrib, hYbw]; abel
      rw [hQ]
      refine Submodule.add_mem _ (Submodule.add_mem _ (B_le_D _ hKVI _ (hbB a)) ?_) ?_
      · exact axisU_le_D _ _ _ (Ne.symm hj) (linefix X ht u h hfix (ww a) (hwW a))
      · refine Submodule.sum_mem _ fun s _ => ?_
        rw [hjj]
        apply tl_mem_D X ht jj
        have := hqD (a, s)
        rw [Dbig_eq, Submodule.mem_iInf] at this
        exact this jj
  · -- the weight bound
    have hYQ : Yt - Q = fun a => ∑ s, tl ht (h s) ((m - q) (a, s)) := by
      funext a; simp [Q]
    have h1 : (wtU (M - Q) : ℝ) ≤ tt (tpt ht) + wtU (Yt - Q) := by
      have := wtU_triangle M Yt Q
      have e2 : wtU (M - Yt) = tt (tpt ht) := hYw _
      exact_mod_cast (by omega : wtU (M - Q) ≤ tt (tpt ht) + wtU (Yt - Q))
    have h2 : (wtU (Yt - Q) : ℝ) ≤ Fintype.card (S t) * wtU (m - q) := by
      rw [hYQ]; exact_mod_cast wt_tl_fam ht h (m - q)
    have h3 : (wtU (m - q) : ℝ) ≤ K' * ∑ i, (lam i : ℝ) := by
      refine hqw.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hK')
      exact_mod_cast hdist i
    have hsplit := sum_split ht (fun j => (tt j : ℝ))
    set T := (tt (tpt ht) : ℝ)
    set SJ := ∑ i : {i // i ∈ I.erase t}, (tt (lift i) : ℝ)
    have hcardJ := card_J ht
    set n := I.card - 1
    have hlam' : ∑ i, (Fintype.card (S t) : ℝ) * (lam i : ℝ) ≤ (SJ + n * T) / P := by
      rw [le_div_iff₀ hP, Finset.sum_mul]
      calc ∑ i, (Fintype.card (S t) : ℝ) * (lam i : ℝ) * P
          ≤ ∑ i : {i // i ∈ I.erase t}, ((tt (lift i) : ℝ) + T) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := hlam i; linarith
        _ = SJ + n * T := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcardJ, nsmul_eq_mul]
    have hS0 : (0 : ℝ) ≤ SJ := Finset.sum_nonneg fun i _ => by positivity
    have hT0 : (0 : ℝ) ≤ T := by positivity
    have hKP : 0 ≤ K' / P := div_nonneg hK' hP.le
    have hmain : (wtU (M - Q) : ℝ) ≤ T + K' / P * (SJ + n * T) := by
      calc (wtU (M - Q) : ℝ) ≤ T + Fintype.card (S t) * (K' * ∑ i, (lam i : ℝ)) := by
            have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ Fintype.card (S t))
            linarith
        _ = T + K' * ∑ i, (Fintype.card (S t) : ℝ) * (lam i : ℝ) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; congr 1
            refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ T + K' * ((SJ + n * T) / P) := by gcongr
        _ = T + K' / P * (SJ + n * T) := by ring
    rw [hsplit]
    have hfin : T + K' / P * (SJ + n * T) ≤ (1 + (n : ℝ) * K' / P) * (T + SJ) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · have : SJ = 0 := by
          have hJ : Fintype.card {i // i ∈ I.erase t} = 0 := by rw [hcardJ]; exact hn
          simp only [SJ]
          rw [Fintype.card_eq_zero_iff] at hJ
          simp
        rw [this, hn]; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have h' : K' / P * SJ ≤ n * (K' / P) * SJ := by
          have := mul_le_mul_of_nonneg_right this (mul_nonneg hKP hS0)
          nlinarith
        have e : (1 + (n : ℝ) * K' / P) * (T + SJ) = T + SJ + n * (K' / P) * T + n * (K' / P) * SJ := by
          ring
        rw [e]
        nlinarith
    linarith

end PrivPCP.L49


namespace PrivPCP.L49

open GoodQLTC Classical PrivPCP.TDual PrivPCP.L46Aux

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

theorem base49 (I : Finset ι) (t : ι) (ht : t ∈ I) (hI : I.erase t = ∅) : RT X I 1 := by
  intro A _ M
  have hall : ∀ j : {i // i ∈ I}, j = tpt ht := by
    intro j
    apply Subtype.ext
    by_contra h
    have : j.val ∈ I.erase t := Finset.mem_erase.2 ⟨h, j.2⟩
    rw [hI] at this; simp at this
  obtain ⟨Y, hY, hYw⟩ := exists_distU M ((X.restrict I).D (tpt ht))
  refine ⟨Y, fun a => ?_, ?_⟩
  · rw [Dbig_eq, Submodule.mem_iInf]
    intro j; rw [hall j]; exact hY a
  · rw [one_mul, hYw]
    exact Finset.single_le_sum (f := fun j => (distU M ((X.restrict I).D j) : ℝ))
      (fun j _ => by positivity) (Finset.mem_univ (tpt ht))

lemma RT_mono (I : Finset ι) (K K' : ℝ) (h : K ≤ K') (hK : RT X I K) : RT X I K' := by
  intro A _ M
  obtain ⟨Q, hQ, hw⟩ := hK A M
  refine ⟨Q, hQ, hw.trans ?_⟩
  exact mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun i _ => by positivity)

/-! transport to the full grid -/

lemma E_push (I : Finset ι) (hI : ∀ i, i ∈ I) (j : ι) (x : (∀ i, S i) → F) (hx : x ∈ X.E j) :
    (fun ω => x (Ti I hI ω)) ∈ (X.restrict I).E ⟨j, hI j⟩ := by
  unfold NestedCodes.E tensorCode at hx ⊢
  rw [Submodule.mem_iInf] at hx ⊢
  intro m
  have := axis_push I hI (Function.update X.V j (X.K j)) m.val x (hx m.val)
  have hfam : (fun i : {i // i ∈ I} => Function.update X.V j (X.K j) i.val) =
      Function.update (X.restrict I).V ⟨j, hI j⟩ ((X.restrict I).K ⟨j, hI j⟩) := by
    funext i
    by_cases h : i.val = j
    · have hi : i = ⟨j, hI j⟩ := Subtype.ext h
      subst hi; simp; rfl
    · have h' : i ≠ ⟨j, hI j⟩ := fun e => h (congrArg Subtype.val e)
      rw [Function.update_of_ne h', Function.update_of_ne h]; rfl
  rw [hfam] at this
  exact this

lemma E_pull (I : Finset ι) (hI : ∀ i, i ∈ I) (j : {i // i ∈ I}) (x : Om S I → F)
    (hx : x ∈ (X.restrict I).E j) : (fun ω => x (Tm I ω)) ∈ X.E j.val := by
  unfold NestedCodes.E tensorCode at hx ⊢
  rw [Submodule.mem_iInf] at hx ⊢
  intro m
  have hfam : Function.update (X.restrict I).V j ((X.restrict I).K j) =
      fun i : {i // i ∈ I} => Function.update X.V j.val (X.K j.val) i.val := by
    funext i
    by_cases h : i = j
    · subst h; simp; rfl
    · have h' : i.val ≠ j.val := fun e => h (Subtype.ext e)
      rw [Function.update_of_ne h, Function.update_of_ne h']; rfl
  have := hx ⟨m, hI m⟩
  rw [hfam] at this
  exact axis_pull I hI _ ⟨m, hI m⟩ x this

lemma Dbig_pull (I : Finset ι) (hI : ∀ i, i ∈ I) (Q : Om S I → F)
    (hQ : Q ∈ (X.restrict I).Dbig) : (fun ω => Q (Tm I ω)) ∈ X.Dbig := by
  intro x hx
  rw [dotProduct_comm, dot_T I hI]
  rw [dotProduct_comm]
  apply hQ
  refine Submodule.iSup_induction _ (motive := fun x => (fun ω => x (Ti I hI ω)) ∈
    (X.restrict I).Kbig) hx ?_ ?_ ?_
  · intro j x hxj
    exact Submodule.mem_iSup_of_mem _ (E_push X I hI j x hxj)
  · exact Submodule.zero_mem _
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

lemma D_push (I : Finset ι) (hI : ∀ i, i ∈ I) (i : ι) (Yv : (∀ i, S i) → F) (hY : Yv ∈ X.D i) :
    (fun ω => Yv (Ti I hI ω)) ∈ (X.restrict I).D ⟨i, hI i⟩ := by
  intro x hx
  rw [← dot_T I hI]
  exact hY _ (E_pull X I hI ⟨i, hI i⟩ x hx)

lemma supportCard_T (I : Finset ι) (hI : ∀ i, i ∈ I) (z : (∀ i, S i) → F) :
    supportCard (fun ω => z (Ti I hI ω)) = supportCard z := by
  unfold supportCard
  refine Finset.card_nbij' (Ti I hI) (Tm I) ?_ ?_ ?_ ?_
  · intro ω hω; simpa using hω
  · intro ω hω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    simpa [Ti_Tm] using hω
  · intro ω _; exact Tm_Ti I hI ω
  · intro ω _; exact Ti_Tm I hI ω

lemma wtU_unit {α : Type} [Fintype α] (z : Unit → α → F) : wtU z = supportCard (z ()) := by
  rw [wtU_eq]
  unfold supportCard
  congr 1; ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  constructor
  · rintro ⟨⟨⟩, h⟩; exact h
  · intro h; exact ⟨(), h⟩

theorem transport49 (I : Finset ι) (hI : ∀ i, i ∈ I) (K : ℝ) (hK0 : 0 ≤ K) (hK : RT X I K)
    (M : (∀ i, S i) → F) :
    (distTo M X.Dbig : ℝ) ≤ K * ∑ i, (distTo M (X.D i) : ℝ) := by
  obtain ⟨Q', hQ', hw⟩ := hK Unit (fun _ ω => M (Ti I hI ω))
  set Q : (∀ i, S i) → F := fun ω => Q' () (Tm I ω)
  have hQ : Q ∈ X.Dbig := Dbig_pull X I hI (Q' ()) (hQ' ())
  have h1 : distTo M X.Dbig ≤ supportCard (M - Q) := Nat.sInf_le ⟨Q, hQ, rfl⟩
  have h2 : supportCard (M - Q) = wtU ((fun _ ω => M (Ti I hI ω)) - Q') := by
    rw [wtU_unit, ← supportCard_T I hI]
    congr 1
  have h3 : ∀ i : {i // i ∈ I}, distU (fun (_ : Unit) ω => M (Ti I hI ω)) ((X.restrict I).D i) ≤
      distTo M (X.D i.val) := by
    intro i
    obtain ⟨Yv, hYv, hYw⟩ := Nat.sInf_mem (s := {d | ∃ y ∈ X.D i.val, supportCard (M - y) = d})
      ⟨_, 0, Submodule.zero_mem _, rfl⟩
    have hmem := D_push X I hI i.val Yv hYv
    refine (distU_le _ _ (fun _ ω => Yv (Ti I hI ω)) (fun _ => hmem)).trans ?_
    rw [wtU_unit]
    show _ ≤ sInf _
    rw [← hYw, ← supportCard_T I hI]
    rfl
  calc (distTo M X.Dbig : ℝ) ≤ wtU ((fun _ ω => M (Ti I hI ω)) - Q') := by
        rw [← h2]; exact_mod_cast h1
    _ ≤ K * ∑ i, (distU (fun (_ : Unit) ω => M (Ti I hI ω)) ((X.restrict I).D i) : ℝ) := hw
    _ ≤ K * ∑ i : {i // i ∈ I}, (distTo M (X.D i.val) : ℝ) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => by exact_mod_cast h3 i) hK0
    _ = K * ∑ i, (distTo M (X.D i) : ℝ) := by
        congr 1
        exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv hI) _ _ (fun i => rfl)

end PrivPCP.L49


namespace PrivPCP.L49

lemma P_mono (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (m k : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) :
    ρ ^ k / (k * (2 ^ k + 1) ^ k) ≤ ρ ^ m / (m * (2 ^ m + 1) ^ m) := by
  have h1 : ρ ^ k ≤ ρ ^ m := pow_le_pow_of_le_one hρ.le hρ1 hmk
  have h2 : (m : ℝ) * (2 ^ m + 1) ^ m ≤ k * (2 ^ k + 1) ^ k := by
    have a1 : (m : ℝ) ≤ k := by exact_mod_cast hmk
    have a2 : ((2 : ℝ) ^ m + 1) ^ m ≤ (2 ^ k + 1) ^ k := by
      calc ((2 : ℝ) ^ m + 1) ^ m ≤ (2 ^ k + 1) ^ m := by
            gcongr
            · norm_num
        _ ≤ (2 ^ k + 1) ^ k := pow_le_pow_right₀ (by have h : (0:ℝ) ≤ 2 ^ k := (by positivity); linarith) hmk
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have : (0 : ℝ) ≤ (2 ^ m + 1) ^ m := by positivity
    nlinarith
  have hpos : (0 : ℝ) < m * (2 ^ m + 1) ^ m := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  calc ρ ^ k / (k * (2 ^ k + 1) ^ k) ≤ ρ ^ m / (k * (2 ^ k + 1) ^ k) := by
        gcongr
    _ ≤ ρ ^ m / (m * (2 ^ m + 1) ^ m) := by
        apply div_le_div_of_nonneg_left (by positivity) hpos h2

lemma const_bound (k : ℕ) (hk : 2 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((k : ℝ) / (ρ ^ k / (k * (2 ^ k + 1) ^ k))) ^ (k - 1) ≤
      Real.exp (10 * ((k : ℝ) ^ 3 + (k : ℝ) ^ 2 * Real.log (1 / ρ))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hx : (0 : ℝ) < (k : ℝ) / (ρ ^ k / (k * (2 ^ k + 1) ^ k)) := by positivity
  have hlogρ : 0 ≤ Real.log (1 / ρ) := Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  have hlog : Real.log ((k : ℝ) / (ρ ^ k / (k * (2 ^ k + 1) ^ k))) =
      2 * Real.log k + k * Real.log (2 ^ k + 1) + k * Real.log (1 / ρ) := by
    have e : (k : ℝ) / (ρ ^ k / (k * (2 ^ k + 1) ^ k)) = k * k * (2 ^ k + 1) ^ k * (1 / ρ) ^ k := by
      rw [one_div_pow]; field_simp
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  have hlk : Real.log k ≤ k := (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  have hl2 : Real.log ((2 : ℝ) ^ k + 1) ≤ k + 1 := by
    have : (2 : ℝ) ^ k + 1 ≤ 2 ^ (k + 1) := by
      rw [pow_succ]; have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num); linarith
    calc Real.log ((2 : ℝ) ^ k + 1) ≤ Real.log (2 ^ (k + 1)) :=
          Real.log_le_log (by positivity) this
      _ = (k + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      _ ≤ (k + 1) * 1 := by
          gcongr
          exact (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      _ = k + 1 := by ring
  rw [← Real.exp_log (pow_pos hx (k - 1)), Real.log_pow, hlog]
  apply Real.exp_le_exp.2
  have hkm : ((k - 1 : ℕ) : ℝ) ≤ k := by
    rw [Nat.cast_sub (by omega)]; simp
  have hkm0 : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by positivity
  have hinner : 2 * Real.log k + k * Real.log (2 ^ k + 1) + k * Real.log (1 / ρ) ≤
      4 * (k : ℝ) ^ 2 + k * Real.log (1 / ρ) := by
    have : (k : ℝ) * Real.log (2 ^ k + 1) ≤ k * (k + 1) := mul_le_mul_of_nonneg_left hl2 hk0.le
    nlinarith
  have hinner0 : 0 ≤ 4 * (k : ℝ) ^ 2 + k * Real.log (1 / ρ) := by positivity
  calc ((k - 1 : ℕ) : ℝ) * (2 * Real.log k + k * Real.log (2 ^ k + 1) + k * Real.log (1 / ρ))
      ≤ ((k - 1 : ℕ) : ℝ) * (4 * (k : ℝ) ^ 2 + k * Real.log (1 / ρ)) :=
        mul_le_mul_of_nonneg_left hinner hkm0
    _ ≤ (k : ℝ) * (4 * (k : ℝ) ^ 2 + k * Real.log (1 / ρ)) :=
        mul_le_mul_of_nonneg_right hkm hinner0
    _ ≤ 10 * ((k : ℝ) ^ 3 + (k : ℝ) ^ 2 * Real.log (1 / ρ)) := by
        have : (0 : ℝ) ≤ (k : ℝ) ^ 2 * Real.log (1 / ρ) := by positivity
        nlinarith

end PrivPCP.L49

open PrivPCP PrivPCP.L49 PrivPCP.L46Aux GoodQLTC Classical

theorem solution : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (F : Type) [Field F] [Fintype F] (k : ℕ), 2 ≤ k →
    ∀ (S : Fin k → Type) [∀ i, Fintype (S i)] (X : NestedCodes F (Fin k) S), X.Valid →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (∀ I : Finset (Fin k), 2 ≤ I.card → ∀ b : Fin k → Bool,
        GoodQLTC.IsProductExpanding ρ ((X.restrict I).mixed fun i => b i.val)) →
      ∀ M : (∀ i, S i) → F,
        (distTo M X.Dbig : ℝ) ≤ Real.exp (C₀ * (k ^ 3 + k ^ 2 * Real.log (1 / ρ))) * ∑ i, (distTo M (X.D i) : ℝ) := by
  refine ⟨10, by norm_num, ?_⟩
  intro F _ _ k hk S _ X hX ρ hρ hρ1 hPE M
  have hKV : ∀ i, X.K i ≤ X.V i := fun i => (hX i).2.le
  set P : ℝ := ρ ^ k / (k * (2 ^ k + 1) ^ k) with hPdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hP : 0 < P := by positivity
  have hP1 : P ≤ 1 := by
    rw [hPdef, div_le_one (by positivity)]
    have h1 : ρ ^ k ≤ 1 := pow_le_one₀ hρ.le hρ1
    have h2 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have h3 : (1 : ℝ) ≤ (2 ^ k + 1) ^ k := one_le_pow₀ (by have h : (0:ℝ) ≤ 2 ^ k := (by positivity); linarith)
    nlinarith
  let Iset : Fin k → Finset (Fin k) := fun t => Finset.univ.filter fun i => t ≤ i
  have hmem : ∀ t : Fin k, t ∈ Iset t := fun t => by simp [Iset]
  have hcardI : ∀ t : Fin k, (Iset t).card = k - t.val := by
    intro t
    have : Iset t = Finset.Ici t := by ext i; simp [Iset]
    rw [this, Fin.card_Ici]
  have hKP : (1 : ℝ) ≤ k / P := by
    rw [le_div_iff₀ hP]
    have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have chain : ∀ n : ℕ, ∀ t : Fin k, t.val + n = k - 1 → RT X (Iset t) ((k / P) ^ n) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have herase : (Iset t).erase t = ∅ := by
        ext i
        simp only [Iset, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and]
        intro hne hle
        have : t.val < i.val := lt_of_le_of_ne hle (fun e => hne (Fin.ext e).symm)
        have := i.isLt
        omega
      rw [pow_zero]
      exact base49 X (Iset t) t (hmem t) herase
    | succ n ih =>
      intro t ht
      have ht1 : t.val + 1 < k := by omega
      set t' : Fin k := ⟨t.val + 1, ht1⟩
      have herase : (Iset t).erase t = Iset t' := by
        ext i
        simp only [Iset, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, t']
        constructor
        · rintro ⟨hne, hle⟩
          have : t.val < i.val := lt_of_le_of_ne hle (fun e => hne (Fin.ext e).symm)
          show t.val + 1 ≤ i.val; omega
        · intro h
          have h' : t.val + 1 ≤ i.val := h
          refine ⟨fun e => ?_, ?_⟩
          · rw [e] at h'; omega
          · show t.val ≤ i.val; omega
      have IH := ih t' (by simp [t']; omega)
      rw [← herase] at IH
      have hcard2 : 2 ≤ (Iset t).card := by rw [hcardI]; omega
      have hCPE : ∀ i : {i // i ∈ (Iset t).erase t}, IsCollectivelyPE P (mix2 X (Iset t) t i.val) := by
        intro i
        have hpe := hPE (Iset t) hcard2 (fun j => decide (j ≠ i.val ∧ j ≠ t))
        have hc := cpe_generic (by rw [Fintype.card_coe]; omega) ρ ⟨hρ, hρ1⟩ _ hpe
        rw [Fintype.card_coe] at hc
        refine cpe_mono _ _ P hP.le ?_ hc
        exact P_mono ρ hρ hρ1 _ k (by omega) (by rw [hcardI]; omega)
      have hstep := step49 X hKV (Iset t) t (hmem t) P ((k / P) ^ n) hP (by positivity) hCPE IH
      refine RT_mono X _ _ _ ?_ hstep
      rw [hcardI]
      have hcn : ((k - t.val - 1 : ℕ) : ℝ) = n + 1 := by
        have : k - t.val - 1 = n + 1 := by omega
        rw [this]; push_cast; ring
      rw [hcn, pow_succ]
      have hx : (1 : ℝ) ≤ (k / P) ^ n := one_le_pow₀ hKP
      have hnk : (n : ℝ) + 2 ≤ k := by
        have : n + 2 ≤ k := by omega
        exact_mod_cast this
      have e1 : (n + 1 : ℝ) * (k / P) ^ n / P = (n + 1) / P * (k / P) ^ n := by ring
      rw [e1]
      have e2 : (k / P) ^ n * (k / P) = k / P * (k / P) ^ n := by ring
      rw [e2]
      have h1P : 1 ≤ 1 / P := by rw [le_div_iff₀ hP]; linarith
      have : (k : ℝ) / P - (n + 1) / P ≥ 1 / P := by
        rw [div_sub_div_same, ge_iff_le]
        exact div_le_div_of_nonneg_right (by linarith) hP.le
      nlinarith
  have h0 := chain (k - 1) ⟨0, by omega⟩ (by simp)
  have hall : ∀ i, i ∈ Iset ⟨0, by omega⟩ := fun i => by
    simp only [Iset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.mk_le_of_le_val (Nat.zero_le _)
  have ht := transport49 X (Iset ⟨0, by omega⟩) hall _ (by positivity) h0 M
  refine ht.trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => by positivity)
  have := const_bound k hk ρ hρ hρ1
  convert this using 3


